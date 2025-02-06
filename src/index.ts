import {readFile} from 'fs/promises';
import { input, confirm  } from '@inquirer/prompts';
import commandLineArgs, {CommandLineOptions, OptionDefinition} from 'command-line-args'
import {
  Condition,
  evalVariablesInToken,
  Field,
  FieldType,
  GenericCondition,
  ProductionNode,
  Rete,
  Token,
  WME
} from 'rete-next/index';
import {ParseError, parseRete, ParseSuccess} from 'rete-next/productions0';
import {AggregateCondition, NegativeCondition, PositiveCondition} from "rete-next";

type ProductionJustification = {
  token:Token,
  prod: string,
};
type AxiomaticJustification = {
  axiomatic: true,
}
type Justification = ProductionJustification | AxiomaticJustification;
type ProductionSpec = {
  production: ProductionNode,
  rhsAssert?: GenericCondition[],
}
type ConflictItem = {
  productionSpec: ProductionSpec,
  tokensToAddOrRemove: [Token[], Token[]],
}
type Query = {
  lhs: GenericCondition[],
  variables: string[],
}
type WMEJustification = {
  wme: WME,
  justifications: Justification[],
};

type conflictResolutionFunction = (conflicts: ConflictItem[]) => ConflictItem | undefined;
type conflictResolutionStrategy = {
  name: string,
  fnc: conflictResolutionFunction,
}

type PatternsForAttribute = {
  id: undefined | string,
  val: undefined | string,
}

interface Options extends CommandLineOptions{
  file: string,
  strategy: string,
  schemaCheck: boolean,
  interactive: boolean,
}

const optionDefinitions: OptionDefinition[] = [
  { name: 'file', alias: 'f', type: String, defaultOption: true},
  { name: 'strategy', alias: 's', type: String},
  { name: 'schema-check', alias: 'c', type: Boolean, defaultValue: false},
  { name: 'interactive', alias: 'i', type: Boolean, defaultValue: false},
];

const options = commandLineArgs(optionDefinitions) as Options;

if(!options.file) {
  console.warn('Options');
  console.warn('  -f, --file           File with Rete productions');
  console.warn('  -s, --strategy       Conflict resolution strategy [optional]');
  console.warn('  -c, --schema-check   Enable schema check before reading file [optional]');
  console.warn('  -i, --interactive    Launch interactive session after running [optional]');
  process.exit();
}

const rete = new Rete();

const productions: ProductionSpec[] = [];
let stratumBeingRead = 0;
let strata: ProductionSpec[][] = [[]];
const queries: Query[] = [];
let justifications: WMEJustification[] = [];
let nonDeterministicFixpointPossible = false;
const patternsForAttributes: {[attr:string]:PatternsForAttribute[]} = {};
let schemaCheck = options.schemaCheck;

function tryMatchPatternInWME(wme: WME, patternsForAttribute: PatternsForAttribute[]) {
  for (const patternForAttribute of patternsForAttribute) {
    const {id, val} = patternForAttribute;
    let ok = true;
    if(id) {
      const idPat = wme.fields[0];
      ok &&= id === idPat;
    }
    if(val) {
      const valPat = wme.fields[2];
      ok &&= val === valPat;
    }
    if(ok) {
      return true;
    }
  }
  return false;
}

function tryMatchPatternInCondition(cond: Condition, patternsForAttribute: PatternsForAttribute[]) {
  for (const patternForAttribute of patternsForAttribute) {
    const {id, val} = patternForAttribute;
    let okId = true;
    let okVal = true;
    if(id && cond.attrs[0] instanceof Field && (cond.attrs[0] as Field).type === FieldType.Const) {
      const idPat = (cond.attrs[0] as Field).v;
      okId= id === idPat;
    }
    if(val && cond.attrs[2] instanceof Field && (cond.attrs[2] as Field).type === FieldType.Const) {
      const valPat = (cond.attrs[2] as Field).v;
      okVal = val === valPat;
    }
    if(okId && okVal) {
      return true;
    }
  }
  return false;
}

function checkWMEAgainstSchema(wme: WME) {
  const attr = wme.fields[1];
  const patternsForAttribute = patternsForAttributes[attr];
  if (!patternsForAttribute) {
    console.warn(`No schema registered for attribute ${attr}`);
  } else {
    const ok = tryMatchPatternInWME(wme, patternsForAttribute);
    if (!ok) {
      console.warn(`No schema pattern matches WME ${wme.toString()}`);
    }
  }
}

function checkConditionsAgainstSchema(lhs: GenericCondition[]) {
  for (const cond of lhs) {
    if(cond instanceof Condition && cond.attrs[1] instanceof Field && (cond.attrs[1] as Field).type === FieldType.Const) {
      const attr = (cond.attrs[1] as Field).v;
      const patternsForAttribute = patternsForAttributes[attr];
      if(!patternsForAttribute) {
        console.warn(`No schema registered for attribute ${attr}`);
      } else {
        const ok = tryMatchPatternInCondition(cond, patternsForAttribute);
        if(!ok) {
          console.warn(`No schema pattern matches condition ${cond.toString()}`);
        }
      }
      if(cond instanceof AggregateCondition) {
        checkConditionsAgainstSchema(cond.innerConditions);
      }
    } else if('negativeConditions' in cond) { //instanceof does not work!
      checkConditionsAgainstSchema(cond.negativeConditions);
    } else if('positiveConditions' in cond) { //instanceof does not work!
      checkConditionsAgainstSchema(cond.positiveConditions);
    }
  }
}

function parseAndExecute(input: string) {
  const reteParseProductions = parseRete(input);

  if(!('specs' in reteParseProductions)) {
    let parseError = reteParseProductions as ParseError;
    console.error(parseError.error);
    process.exit();
  }
  const parsedProductions = reteParseProductions as ParseSuccess;

  for (const {lhs, rhs, rhsAssert, variables} of parsedProductions.specs) {
    if (!rhs && !rhsAssert && !variables) { //Assert
      let wmes = rete.addWMEsFromConditions(lhs);
      console.log(`Added ${wmes[0].length} WME${wmes[0].length === 1 ? '' : 's'}`);
      for (const wme of wmes[0]) {
        justifications.push({wme, justifications: [{axiomatic: true}]});
        schemaCheck && checkWMEAgainstSchema(wme);
      }
    } else if (variables && !rhsAssert) { //Query
      queries.push({lhs, variables});
      schemaCheck && checkConditionsAgainstSchema(lhs);
    } else if (rhs) {
      const unsafeCondition = !!lhs.find(c => c instanceof AggregateCondition
        || c instanceof NegativeCondition || c instanceof PositiveCondition
      );
      nonDeterministicFixpointPossible ||= unsafeCondition;
      let production = rete.addProduction(lhs, rhs);
      const productionSpec = {
        production,
        rhsAssert,
      };
      productions.push(productionSpec);
      strata[stratumBeingRead].push(productionSpec);
      console.log(`Added production: "${rhs}"`);
      if (schemaCheck) {
        checkConditionsAgainstSchema(lhs);
        rhsAssert && checkConditionsAgainstSchema(rhsAssert);
      }
    }
  }

  if (nonDeterministicFixpointPossible) {
    console.log('Non-deterministic fixpoint cannot be ruled out');
  }
}

const stratumDirective = '#stratum';
const schemaCheckDirective = '#schemacheck';
const schemaDirective = '#schema';

function executeDirective(dir: string) {
  if(dir.startsWith(stratumDirective)) {
    strata.push([]);
    stratumBeingRead++;
    console.log(`Now reading stratum #${stratumBeingRead}`);
  } else if(dir.startsWith(schemaCheckDirective)) {
    const s = dir.substring(schemaCheckDirective.length).trim();
    if(!['on', 'off'].includes(s)) {
      console.warn(`Malformed directive ${dir}`);
      return;
    }
    schemaCheck = s === 'on';
  } else if(dir.startsWith(schemaDirective)) {
    const patterns = dir.substring(schemaDirective.length).trim();
    const strings = patterns.split(' ');
    if(strings.length !== 3 || strings[1] === '_') {
      console.warn(`Malformed directive ${dir}`);
      return;
    }
    const [id, attr, val] = strings;
    if(!patternsForAttributes[attr]) {
      patternsForAttributes[attr] = [];
    }
    patternsForAttributes[attr].push({
      id: id === '_' ? undefined : id,
      val: val === '_' ? undefined : val,
    });
  }
}

function readInputInterpretDirectivesAndParseAndExecute(input) {
  const lines = input.split('\n');
  let clauses = '';
  for (const line of lines) {
    const trimmedLine = line.trim();
    if(trimmedLine.startsWith('#')) {
      executeDirective(trimmedLine);
      if(clauses) {
        parseAndExecute(clauses);
        clauses = '';
      }
    } else {
      clauses += line + '\n';
    }
  }
  if(clauses) {
    parseAndExecute(clauses);
  }
}

let fileContents: string = await readFile(options.file, 'UTF8') as string;

readInputInterpretDirectivesAndParseAndExecute(fileContents);

function firstMatchConflictResolution(conflicts: ConflictItem[]): ConflictItem | undefined {
  return conflicts[0];
}

function stratifiedManual(conflicts: ConflictItem[]): ConflictItem | undefined {
  do {
    const productionRhses = strata[currentStratum].map(x => x.production.rhs);
    const found = conflicts.find(c => productionRhses.includes(c.productionSpec.production.rhs));
    if(found) {
      return found;
    }
    currentStratum++;
  } while(currentStratum < strata.length);
  return undefined;
}

const conflictResolutionStrategies: conflictResolutionStrategy[] = [
  {
    name: 'firstMatch',
    fnc: firstMatchConflictResolution,
  },
  {
    name: 'stratifiedManual',
    fnc: stratifiedManual,
  },
];

let selectedConflictResolutionStrategy = conflictResolutionStrategies[0];

if(!options.strategy) {
  console.log(`No conflict resolution strategy specified, defaulting to: ${selectedConflictResolutionStrategy.name}`);
} else {
  const found = conflictResolutionStrategies.find(crs => crs.name.toLowerCase().startsWith(options.strategy.toLowerCase()));
  if(found) {
    selectedConflictResolutionStrategy = found;
    console.log(`Conflict resolution strategy specified: ${selectedConflictResolutionStrategy.name}`);
  } else {
    console.log(`Conflict resolution strategy specified was not found, defaulting to: ${selectedConflictResolutionStrategy.name}`);
  }
}

function findConflictSet() {
  const conflicts: ConflictItem[] = [];
  for (const productionSpec of productions) {
    const tokensToAddOrRemove = productionSpec.production.canFire();
    if (tokensToAddOrRemove[0].length + tokensToAddOrRemove[1].length) {
      conflicts.push({
        productionSpec,
        tokensToAddOrRemove,
      })
    }
  }
  return conflicts;
}

function run() {
  do {
    console.log(`Cycle ${cycle}`);
    const conflicts = findConflictSet();
    if (conflicts.length === 0) {
      console.log('No more productions');
      break;
    }
    const conflictItem = selectedConflictResolutionStrategy.fnc(conflicts);
    if (!conflictItem) {
      console.log('No more productions');
      break;
    }
    let production = conflictItem.productionSpec.production;
    console.log(production.rhs);
    let [tokensToAdd, tokensToRemove] = production.willFire();
    for (const token of tokensToRemove) {
      const foundJustifications = justifications
        .filter(j => j.justifications
          .filter(jj => 'prod' in jj).map(jj => jj as ProductionJustification)
          .find(jj => jj.prod === production.rhs && jj.token === token));
      for (const foundJustification of foundJustifications) {
        foundJustification.justifications = foundJustification
          .justifications
          .filter(jj => 'prod' in jj).map(jj => jj as ProductionJustification)
          .filter(jj => jj.prod === production.rhs && jj.token !== token);
        if(foundJustification.justifications.length === 0) {
          console.log(`No justifications left, will be removed:`, foundJustification.wme.toString());
          rete.removeWME(foundJustification.wme);
        }
      }
    }
    justifications = justifications.filter(j => j.justifications.length);
    if (conflictItem.productionSpec.rhsAssert) {
      for (const token of tokensToAdd) {
        const variablesInToken = evalVariablesInToken(
          Object.keys(production.locationsOfAllVariablesInConditions),
          production.locationsOfAllVariablesInConditions,
          token
        );
        const wmes = rete.addWMEsFromConditions(conflictItem.productionSpec.rhsAssert, variablesInToken);
        const [wmesAdded, wmesExisting] = wmes;
        for (const wme of wmesAdded) {
          justifications.push({
            wme,
            justifications: [{
              prod: production.rhs,
              token,
            }]
          })
        }
        for (const wme of wmesExisting) {
          let wmeJustification = justifications.find(j => j.wme === wme);
          if(wmeJustification) {
            wmeJustification.justifications.push({
              prod: production.rhs,
              token,
            })
          }
        }
      }
    }
  } while (cycle++ <= MAX_CYCLES);
}

function runQueries() {
  if (queries.length) {
    console.log(`Running ${queries.length} ${queries.length === 1 ? 'query' : 'queries'}`);
    for (const query of queries) {
      const {lhs, variables} = query;
      const stringToStringMaps = rete.query(lhs, variables);
      for (let i = 0; i < stringToStringMaps.length; i++) {
        const stringToStringMap = stringToStringMaps[i];
        let entries = Object.entries(stringToStringMap);
        for (const [key, value] of entries) {
          console.log(`${i}||${key}:${value}`);
        }
      }
    }
  }
}

function showKnowledgeBase() {
  if (justifications.length) {
    console.log(`The working memory consists of ${justifications.length} WMEs`);
    for (const {wme, justifications: j} of justifications) {
      let jStrings = [];
      for (const justification of j) {
        if ('prod' in justification) {
          let productionJustification = justification as ProductionJustification;
          jStrings.push(`[${productionJustification.prod}:${productionJustification.token.toString()}]`);
        } else {
          jStrings.push('[Axiomatic]');
        }
      }
      console.log(`${wme.toString()}: ${jStrings.join(',')}`);
    }
  }
}

function interactiveRetract(prompt: string) {
  const strings = prompt.trim().split(' ');
  if(strings.length === 3) {
    const found = rete.working_memory.find(w => w.fields[0] === strings[0] && w.fields[1] === strings[1] && w.fields[2] === strings[2]);
    const foundJustification = justifications.find(j => j.wme === found);
    if(!found || !foundJustification) {
      console.warn(`No WME found matching (${strings[0]} ${strings[1]} ${strings[2]} )`);
    } else {
      const axiomaticJustification = foundJustification.justifications.find(jj => 'axiomatic' in jj);
      if(!axiomaticJustification) {
        console.warn(`WME does not have an axiomatic justification and cannot be retracted`);
        return;
      }
      foundJustification.justifications = foundJustification.justifications.filter(jj => jj !== axiomaticJustification);
      if (foundJustification.justifications.length === 0) {
        rete.removeWME(found);
        justifications = justifications.filter(j => j !== foundJustification);
      }
      run();
      showKnowledgeBase();
    }
  } else {
    console.error(`Malformed retract command ${prompt}`)
  }
}

async function interactive() {
  console.log('Use "quit", "exit" or "bye" to exit');
  let contextLength = 0;
  do {
    try {
      const answer = await input({message: '>'});
      if (answer.toLowerCase() === 'bye' || answer.toLowerCase() === 'exit' || answer.toLowerCase() === 'quit') {
        console.log('Bye to you, too');
        break;
      }
      if(answer.toLowerCase().startsWith('retract')) {
        interactiveRetract(answer.substring(7));
      }
    } catch (e) {
      console.error(e);
    }
  } while (true);
}

let currentStratum = 0;
const MAX_CYCLES = 100;
let cycle = 1;

run();
runQueries();
showKnowledgeBase();

if(options.interactive) {
  await interactive();
}
