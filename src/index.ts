import {readFile} from 'fs/promises';
import {confirm, input} from '@inquirer/prompts';
import commandLineArgs, {CommandLineOptions, OptionDefinition} from 'command-line-args'
import {OpenAI} from 'openai';
import {
  ChatCompletionAssistantMessageParam,
  ChatCompletionMessageParam,
  ChatCompletionUserMessageParam
} from "openai/resources";
import {
  Condition,
  evalVariablesInToken,
  Field,
  FieldType,
  FuzzySystem,
  FuzzyVariable, FuzzyWME,
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
  description: undefined | string,
}

interface FuzzyValDefinition {
  name: string,
  a: number,
  c: number,
}

interface FuzzyVariableKind {
  name: string,
  definitions: FuzzyValDefinition[],
}

function sigmoid(a: number, c: number, val: number) {
  return 1 / (1 + Math.exp(-a * (val - c)));
}

class DeclaredFuzzyVariable implements FuzzyVariable {
  constructor(public name: string, public fuzzyVariableKind: FuzzyVariableKind) {
  }

  getName(): string {
    return this.name;
  }

  computeMembershipValueForFuzzyValue(fuzzyValue: string, val: number): number {
    const fuzzyValueDefinition = this.getFuzzyValue(fuzzyValue);
    if(fuzzyValueDefinition) {
      return sigmoid(fuzzyValueDefinition.a, fuzzyValueDefinition.c, val);
    }
    return 0;
  }

  computeValueForFuzzyMembershipValue(fuzzyValue: string, μ: number): number {
    return 0;
  }

  isFuzzyValue(fuzzyValue: string): boolean {
    return !!this.getFuzzyValue(fuzzyValue);
  }

  private getFuzzyValue(fuzzyValue: string) {
    return this.fuzzyVariableKind.definitions.find(x => x.name === fuzzyValue);
  }
}

interface Options extends CommandLineOptions{
  file: string,
  strategy: string,
  schemaCheck: boolean,
  interactive: boolean,
}

class MinMaxFuzzySystem implements FuzzySystem {
  computeConjunction(...μs: number[]): number {
    return Math.min(...μs);
  }

  computeDisjunction(...μs: number[]): number {
    return Math.max(...μs);
  }
}
class MultiplicativeFuzzySystem implements FuzzySystem {
  computeConjunction(...μs: number[]): number {
    return μs.reduce((x,y) => x * y, 1);
  }

  computeDisjunction(...μs: number[]): number {
    return 0; //should be x0 + x1 + ... xn - x0*x1*x[n-1] - ... + ... - ... up to x0*x1*xn
  }
}

const openaiapikeyExists = !!process.env.OPENAI_API_KEY;

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
let fuzzySystem: FuzzySystem;
const fuzzyAttrs: string[] = [];
const fuzzyVariableKinds: FuzzyVariableKind[] = [];

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
  if(fuzzyAttrs.includes(attr)) {
    return;
  }
  const patternsForAttribute = patternsForAttributes[attr];
  if (!patternsForAttribute ) {
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
      if(fuzzyAttrs.includes(attr)) {
        return;
      }
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
}

const stratumDirective = '#stratum';
const schemaCheckDirective = '#schemacheck';
const schemaDirective = '#schema';
const fuzzyDirective = '#fuzzy';

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
    if(strings.length < 3 || strings[1] === '_') {
      console.warn(`Malformed directive ${dir}`);
      return;
    }
    const [id, attr, val] = strings;
    if(!patternsForAttributes[attr]) {
      patternsForAttributes[attr] = [];
    }
    const description = strings.slice(3).join(' ');
    patternsForAttributes[attr].push({
      id: id === '_' ? undefined : id,
      val: val === '_' ? undefined : val,
      description: description || undefined,
    });
  } else if(dir.startsWith(fuzzyDirective)) {
    fuzzyDirectiveHandling(dir.substring(fuzzyDirective.length).trim());
  }
}

function fuzzyDirectiveHandling(prompt: string) {
  if(prompt.toLowerCase().startsWith('system')) {
    const s = prompt.substring(6).trim();
    if(s === 'min-max') {
      fuzzySystem = new MinMaxFuzzySystem();
    } else if(s === 'multiplicative') {
      fuzzySystem = new MultiplicativeFuzzySystem();
    } else {
      console.warn(`Unknown fuzzy system ${s}`);
    }
  } else if(prompt.toLowerCase().startsWith('kind')) {
    const defn = prompt.toLowerCase().substring('kind'.length).trim();
    const fistSpace = defn.indexOf(' ');
    if(fistSpace < 0) {
      console.error(`Malformed fuzzy kind command ${prompt}`)
      return;
    }
    const name = defn.substring(0, fistSpace).trim();
    const vals = defn.substring(fistSpace).trim();
    const valueDefinitions = vals.split(',').map(s => s.trim());
    const definitions: FuzzyValDefinition[] = [];
    for (const valueDefinition of valueDefinitions) {
      const [name, def] = valueDefinition.split(':').map(s => s.trim());
      const [fnc, aS, cS] = def.split(' ').map(s => s.trim());
      if(fnc !== 'sigmoid') {
        console.error(`Only 'sigmoid' membership function can be currently used. Invalid function: ${fnc}`);
        return;
      }
      const a = parseFloat(aS);
      const c = parseFloat(cS);
      if(Number.isNaN(a) || Number.isNaN(c)) {
        console.error(`Invalid 'a' and 'c' values for sigmoid function: ${a}, ${c}`);
        return;
      }
      definitions.push({
        name,
        a,
        c
      });
    }
    fuzzyVariableKinds.push({
      name,
      definitions,
    });
  } else if(prompt.toLowerCase().startsWith('var')) {
    const varnamekind = prompt.toLowerCase().substring('var'.length).trim();
    const [varname, kind] = varnamekind.split(' ');
    const found = fuzzyVariableKinds.find(x => x.name === kind);
    if(!found) {
      console.error(`Undeclared fuzzy variable kind ${kind}`)
      return;
    }
    const declaredFuzzyVariable = new DeclaredFuzzyVariable(varname, found);
    rete.addFuzzyVariable(declaredFuzzyVariable);
  } else if(prompt.toLowerCase().startsWith('attr')) {
    const val = prompt.toLowerCase().substring('attr'.length).trim();
    fuzzyAttrs.push(val);
  } else {
    console.error(`Malformed fuzzy command ${prompt}`)
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

function tokenToMu(token: Token): number | undefined {
  const fuzzyWMEs = token.toArray().filter(x => x instanceof FuzzyWME);
  let mu: number | undefined = fuzzyWMEs.length && fuzzySystem ?
    fuzzySystem.computeConjunction(...fuzzyWMEs.flatMap(w => ((w as FuzzyWME).μ))) :
    undefined;
  return mu;
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
        let mu: number | undefined = tokenToMu(token);
        const [wmesAdded, wmesExisting] = rete.addWMEsFromConditions(conflictItem.productionSpec.rhsAssert, variablesInToken, mu);
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
            });
            if(fuzzySystem && wme instanceof FuzzyWME) {
              const mus = wmeJustification.justifications
                .filter(jj => 'prod' in jj)
                .map(jj => jj as ProductionJustification)
                .map(jj => tokenToMu(jj.token))
                .filter(n => n !== undefined)
                .map(n => n as number)
              ;
              const cumulativeMu = fuzzySystem.computeDisjunction(...mus);
              wme.μ = cumulativeMu; //todo propagate to dependent WMEs
            }
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
      if(stringToStringMaps.length) {
        console.log('Yes.');
      } else {
        console.log('No.');
      }
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

function interactiveHelp(prompt: string) {
  const request = prompt.trim();

  function showQuit() {
    console.log(' quit, exit, bye               Exit');
  }

  function showRetract() {
    console.log(' retract [str] [str] [str]     Retract axiomatic justification for WME ([str] [str] [str])');
  }

  function showExplain() {
    console.log(' explain [str] [str] [str]     Explain the justification for WME ([str] [str] [str])');
  }

  function showRun() {
    console.log(' run [clauses]                 Run the clauses provided');
  }

  function showHelp() {
    console.log(' help [command]                Explain how [command] is used');
  }

  function showClear() {
    console.log(' clear                         Reset the chat and start over');
  }

  function showChat() {
    console.log(' [Prompt to chatbot]           Chat with ChatGPT');
  }

  if(!request) {
    console.log('Commands');
    showQuit();
    showRetract();
    showExplain();
    showRun();
    showClear();
    showChat();
    return;
  }
  switch (request) {
    case 'help': {
      showHelp();
      break;
    }
    case 'quit':
    case 'exit':
    case 'bye': {
      showQuit();
      break;
    }
    case 'retract': {
      showRetract();
      break;
    }
    case 'explain': {
      showExplain();
      break;
    }
    case 'run': {
      showRun();
      break;
    }
    case 'clear': {
      showClear();
      break;
    }
    default: console.log(`Unknown command ${prompt}`);
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

function explainWME(found: WME, indentation: string, visited: WME[]) {
  if(visited.includes(found)) {
    let ret = (indentation) + '(*)\n';
    return ret;
  }
  const foundJustification = justifications.find(j => j.wme === found);
  if (!foundJustification) {
    console.warn(`No justification found for (${found.toString()} )`);
    return '';
  } else {
    let ret = '';
    const length = foundJustification.justifications.length;
    for (let i = 0; i < length; i++){
      const linePrefix = (indentation) + ((i < length - 1) ? '├' : '└');
      const jj = foundJustification.justifications[i];
      if ('axiomatic' in jj) {
        const line = linePrefix + '[Axiomatic]\n';
        ret += line;
      } else {
        const newVisited = [...visited, found];
        ret += linePrefix + `[${jj.prod}]\n`;
        const lengthInner = jj.token.toArray().length;
        for (let iInner = 0; iInner < lengthInner; iInner++){
          const linePrefixInner = (indentation) + ((iInner < lengthInner - 1) ? '  ├' : '  └');
          const wme = jj.token.toArray()[iInner];
          ret += linePrefixInner + wme.toString() + '\n';
          const s = explainWME(wme, indentation + '    ', newVisited);
          ret += s;
        }
      }
    }
    return ret;
  }
}

function beautifyExplanation(s: string) {
  const lines = s.split('\n');
  let lineLocations: number[] = [];
  for (let i = lines.length - 1; i >= 0; i--) {
    const line = lines[i];
    const chars = line.split('');
    for (let i1 = 0; i1 < chars.length; i1++){
      const char = chars[i1];
      if(char === '└') {
        lineLocations.push(i1);
      } else if(lineLocations.includes(i1)) {
        if (char === ' ') {
          chars[i1] = '│';
        } else if(char !== '├') {
          lineLocations = lineLocations.filter(x => x !== i1);
          break;
        }
      }
    }
    lines[i] = chars.join('');
  }
  return lines.join('\n');
}

function interactiveExplain(prompt: string) {
  const strings = prompt.trim().split(' ');
  if(strings.length === 3) {
    const found = rete.working_memory.find(w => w.fields[0] === strings[0] && w.fields[1] === strings[1] && w.fields[2] === strings[2]);
    if (!found) {
      console.warn(`No WME found matching (${strings[0]} ${strings[1]} ${strings[2]} )`);
    } else {
      console.log(found.toString());
      const s = explainWME(found, '', []);
      const explanation = beautifyExplanation(s);
      console.log(explanation);
    }
  } else {
    console.error(`Malformed explain command ${prompt}`)
  }
}

function interactiveRun(prompt: string) {
  readInputInterpretDirectivesAndParseAndExecute(prompt);
  run();
  showKnowledgeBase();
}

interface OpenAiState {
  contextLength: number,
  history: HistoryItem[];
}

let openai: OpenAI;
const openAiState: OpenAiState = {
  contextLength: 0,
  history: [],
}

interface HistoryItem {
  prompt: ChatCompletionUserMessageParam,
  promptTokens: number,
  response: ChatCompletionAssistantMessageParam,
  responseTokens: number,
}

const CONTEXT_TOKENS = 200; //a lot less than the allowed total number of tokens

function createContextOfLength(n: number): ChatCompletionMessageParam[] {
  n --;
  let remainingTokens = CONTEXT_TOKENS;
  const messages: ChatCompletionMessageParam[] = [];
  for (let i = 0; i < openAiState.history.length; i++){
    if(i > n) break;
    const historyItem = openAiState.history[i];
    if(historyItem.responseTokens > remainingTokens) break;
    messages.push({
      role: 'assistant',
      content: historyItem.response.content,
    } as ChatCompletionAssistantMessageParam);
    remainingTokens -= historyItem.responseTokens;

    if(historyItem.promptTokens > remainingTokens) break;
    messages.push({
      role: 'user',
      content: historyItem.prompt.content,
    } as ChatCompletionUserMessageParam);
    remainingTokens -= historyItem.promptTokens;
  }

  return messages;
}

async function getOpenAiResponse(system: string, user: string, contextLength = 0) {
  let messages: ChatCompletionMessageParam[] = [{
    role: 'system',
    content: system,
  }];
  let contextOfLength = createContextOfLength(contextLength);
  // console.log(`Context of length ${contextLength}`, contextOfLength);
  if(contextOfLength.length) {
    messages = [...messages, ...contextOfLength];
  }
  let userMessage: ChatCompletionUserMessageParam = {
    role: 'user',
    content: user
  };
  messages.push(userMessage);
  // console.log('Messages', messages);
  const response = await openai.chat.completions.create({
    model: 'gpt-4o-mini',
    messages,
  });
  openAiState.history.push({
    prompt: userMessage,
    promptTokens: response.usage?.prompt_tokens || 0,
    response: response.choices[0].message,
    responseTokens: response.usage?.completion_tokens || 0,
  });
  return response.choices[0].message;
}

function createSystemPrompt(schemaDescription: string) {
  return `Please use the following triplet notation for Datalog queries:

- **Triplet Structure:** Represent relationships as triplets within parentheses, without commas. Each triplet follows the format: \`(subject predicate object)\`.
  
- **Variables:** Enclose all variables within angle brackets \`< >\`. Examples of variables include \`<m>\`, \`<f>\`, \`<c>\`, \`<c2>\`, etc.
  
- **Constants:** Write constants (specific entities or known values) without angle brackets. For example, \`Esau\`.
  
- **No Commas in Triplets:** Do not use commas inside the triplets. The components are separated by spaces only.
  
- **Query Formation:** Combine multiple triplets to set conditions or express relationships. Use \`->\` to denote the result or output of the query.
  
- **Output Variables:** After the \`->\`, list the variables to output, separated by commas without additional parentheses or angle brackets. If there are no variables, i.e. it is a yes/no question, just finish with the arrow (\`->\`).

**Examples for sample predicates \`mother\`, \`father\`:**

1. **Identifying Husband and Wife:**

   \`\`\`
   (<m> mother <c>) (<f> father <c>) -> <m>,<f>
   \`\`\`
   
   - **Explanation:** Finds \`<m>\` and \`<f>\` who are the mother and father of the same child \`<c>\`, indicating they are husband and wife.

2. **Finding the Mother of Esau:**

   \`\`\`
   (<m> mother Esau) -> <m>
   \`\`\`
   
   - **Explanation:** Retrieves \`<m>\`, the mother of Esau.

3. **Identifying Siblings:**

   \`\`\`
   (<m> mother <c>) (<f> father_o <c>) (<m> mother <c2>) (<f> father <c2>) -> <c>,<c2>
   \`\`\`
   
   - **Explanation:** Finds \`<c>\` and \`<c2>\` who are siblings, sharing the same mother \`<m>\` and father \`<f>\`.

**Guidelines:**

- When constructing or interpreting Datalog queries, always adhere to this notation.
- Ensure clarity by maintaining consistent use of variables and constants.
- Use this format to express complex queries by combining multiple triplets and specifying the desired output.
-------------------------------------------------------------------------------
**Schema of the Knowledge Base**

The following predicates are available:

${schemaDescription}
---

**Additional Guidance**

When constructing queries:

- **Ensure Constraints are Met**: Always use the allowed values for predicate objects when constraints are specified.
- **Use Consistent Naming**: Be consistent with variable names to avoid confusion.
- **Check Validity**: Verify that each triplet adheres to the schema to prevent errors.

**Benefits of Including the Schema**

- **Clarity**: Users clearly understand how to use each predicate and what values are permissible.
- **Error Reduction**: Minimizes the risk of constructing invalid queries that the system cannot process.
- **Ease of Use**: Users can reference the schema as a guide while formulating their queries.
-----------------------------------------------------------------------------------------------------
If you understand what the user wants, respond with the query inside triple quotes. If you don't, ask for clarifications.
`;
}

function queryExtractor(s: string): string | null {
  let lines= s.split('\n');
  let query = null;
  let parsing = false;
  for (const line of lines) {
    const trimmedLine = line.trim();
    if(!parsing && line.startsWith('```')) {
      query = '';
      parsing = true;
    } else if(parsing) {
      if(line.startsWith('```')) {
        parsing = false;
      } else {
        query += line + '\n';
      }
    }
  }
  query = query?.trim();
  if (!query) {
    return null;
  } else {
    if(query[query.length - 1] === ';') query = query.substring(0, query.length - 2);
    return query;
  }
}

function parseAndRunQuery(input: string) {
  const reteParse = parseRete(input);
  if('specs' in reteParse) {
    for (const {lhs, variables} of reteParse.specs) {
      console.log(`Running: (${lhs.map(c => c.toString()).join(' ')}) -> ${(variables as string[]).map(v => '<' + v + '>').join(', ')})`);
      const stringToStringMaps = rete.query(lhs, variables!);
      if(stringToStringMaps.length) {
        console.log('Yes.');
      } else {
        console.log('No.');
      }
      for (let i = 0; i < stringToStringMaps.length; i++){
        const stringToStringMap = stringToStringMaps[i];
        let entries = Object.entries(stringToStringMap);
        for (const [key, value] of entries) {
          console.log(`${i}||${key}:${value}`);
        }
      }
    }
  } else {
    let parseError = reteParse as ParseError;
    console.log(parseError.error);
  }
}

function createSchemaDescription() {
  let schemaDescr = '';
  for (let i = 0; i < Object.entries(patternsForAttributes).length; i++){
    const [attribute, patterns] = (Object.entries(patternsForAttributes))[i];
    let constraints: string;
    if(patterns.length === 1 && !patterns[0].id && !patterns[0].val) {
      constraints = `Unconstrained. ${patterns[0].description || ''}`;
    } else {
      constraints = '\n';
      if(patterns[0].id) {
        constraints += 'The subject can take values: ' + patterns.map(({id, description}) => id + (description ? ` [_ ${attribute} _ meaning: ${description}]` : '')).join(',');
      } else {
        constraints += 'The object can take values: ' + patterns.map(({val, description}) => val + (description ? ` [_ ${attribute} _ meaning: ${description}]` : '')).join(',');
      }
    }
    const attributeDescription = `${i + 1}. **\`${attribute}\`**: ${constraints}
 
`;
    schemaDescr += attributeDescription;
  }
  return schemaDescr;
}

function interactiveClear() {
  openAiState.contextLength = 0;
}

async function interactiveChat(prompt: string) {
  if(!openaiapikeyExists) {
    console.log('OPENAI_API_KEY not found. OpenAI integration has been disabled');
    return;
  }
  if (!openai) {
    let b = await confirm({message: 'Do you want to start a chat session? This will incur costs against your OpenAI credits.'});
    if(!b) {
      return;
    }
    openai = new OpenAI();
  }
  const schemaDescription = createSchemaDescription();
  // console.log(schemaDescription);
  let response = await getOpenAiResponse(createSystemPrompt(schemaDescription), prompt, openAiState.contextLength);
  // console.log('Response', response);
  console.log(response.content);
  let query = response.content && queryExtractor(response.content);
  if (query) {
    let b = await confirm({message: 'Run?'});
    if (b) {
      parseAndRunQuery('(' + query + ')');
    }
  }
  openAiState.contextLength++;
}

async function interactive() {
  console.log('Use "quit", "exit" or "bye" to exit, "help" for a description of available commands.');
  do {
    try {
      const answer = (await input({message: (openAiState.contextLength ? `[${openAiState.contextLength}]` : '') + '>'})).trim();
      if(!answer) {
        console.log(`It seems like your message was empty. Could you please provide the command, Rete-next clauses or English queries you would like assistance with?`);
        continue;
      }
      if (answer.toLowerCase() === 'bye' || answer.toLowerCase() === 'exit' || answer.toLowerCase() === 'quit') {
        console.log('Have a nice day');
        break;
      }
      if(answer.toLowerCase().startsWith('help')) {
        interactiveHelp(answer.substring(4));
      } else if(answer.toLowerCase().startsWith('retract')) {
        interactiveRetract(answer.substring(7));
      } else if(answer.toLowerCase().startsWith('explain')) {
        interactiveExplain(answer.substring(7));
      } else if(answer.toLowerCase().startsWith('run')) {
        interactiveRun(answer.substring(3));
      } else if(answer.toLowerCase() === 'clear') {
        interactiveClear();
      } else {
        await interactiveChat(answer);
      }
    } catch (e) {
      console.error(e);
    }
  } while (true);
}

readInputInterpretDirectivesAndParseAndExecute(fileContents);

if (nonDeterministicFixpointPossible) {
  console.log('Non-deterministic fixpoint cannot be ruled out');
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
