import {readFile} from 'fs/promises';
import {
  evalVariablesInToken,
  GenericCondition,
  ProductionNode,
  Rete,
  Token,
  WME
} from 'rete-next/index';
import {ParseError, parseRete, ParseSuccess} from 'rete-next/productions0';
import {AggregateCondition, NegativeCondition, PositiveCondition} from "rete-next";

if(process.argv.length < 3) {
  console.warn('Usage: node index.js <file with Rete productions>');
  process.exit();
}

let input: string = await readFile(process.argv[2], 'UTF8') as string;

const reteParseProductions = parseRete(input);

if(!('specs' in reteParseProductions)) {
  let parseError = reteParseProductions as ParseError;
  console.error(parseError.error);
  process.exit();
}

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
  init: () => void,
  fnc: conflictResolutionFunction,
}

const rete = new Rete();
const parsedProductions = reteParseProductions as ParseSuccess;
const productions: ProductionSpec[] = [];
const queries: Query[] = [];
let justifications: WMEJustification[] = [];
let nonDeterministicFixpointPossible = false;

for(const {lhs, rhs, rhsAssert, variables} of parsedProductions.specs) {
  if(!rhs && !rhsAssert && !variables) { //Assert
    let wmes = rete.addWMEsFromConditions(lhs);
    console.log(`Added ${wmes[0].length} WME${wmes[0].length === 1?'':'s'}`);
    for (const wme of wmes[0]) {
      justifications.push({wme, justifications: [{axiomatic: true}]});
    }
  } else if(variables && !rhsAssert) { //Query
    queries.push({lhs, variables})
  } else if(rhs) {
    const unsafeCondition = !!lhs.find(c => c instanceof AggregateCondition
      || c instanceof NegativeCondition || c instanceof PositiveCondition
    );
    nonDeterministicFixpointPossible ||= unsafeCondition;
    let production = rete.addProduction(lhs, rhs);
    productions.push({
      production,
      rhsAssert,
    });
    console.log(`Added production: "${rhs}"`);
  }
}

if(nonDeterministicFixpointPossible) {
  console.log('Non-deterministic fixpoint cannot be ruled out');
}

function firstMatchConflictResolution(conflicts: ConflictItem[]): ConflictItem | undefined {
  return conflicts[0];
}

let currentStratum = 0;
let strata: ProductionSpec[][];

function createStrata() {
  let strataCount = 0;
  for (const productionSpec of productions) {
    const rhs = productionSpec.production.rhs;
    const strings = rhs.split('.');
    const number = Number.parseInt(strings[0]);
    if(!Number.isNaN(number)) {
      if(strataCount < number) {
        strataCount = number;
      }
    }
  }
  strata = new Array(strataCount);
  for (const productionSpec of productions) {
    const rhs = productionSpec.production.rhs;
    const strings = rhs.split('.');
    const number = Number.parseInt(strings[0]);
    if(!Number.isNaN(number)) {
      if(!strata[number-1]) {
        strata[number-1] = [];
      }
      strata[number-1].push(productionSpec);
    }
  }
}

function stratifiedManual(conflicts: ConflictItem[]): ConflictItem | undefined {
  if(!strata) {
    createStrata();
  }
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
    init: () => {},
    fnc: firstMatchConflictResolution,
  },
  {
    name: 'stratifiedManual',
    init: createStrata,
    fnc: stratifiedManual,
  },
];

let selectedConflictResolutionStrategy = conflictResolutionStrategies[0];

if(!process.argv[3]) {
  console.log(`No conflict resolution strategy specified, defaulting to: ${selectedConflictResolutionStrategy.name}`);
} else {
  const found = conflictResolutionStrategies.find(crs => crs.name.toLowerCase().startsWith(process.argv[3].toLowerCase()));
  if(found) {
    selectedConflictResolutionStrategy = found;
    console.log(`Conflict resolution strategy specified: ${selectedConflictResolutionStrategy.name}`);
  } else {
    console.log(`Conflict resolution strategy specified was not found, defaulting to: ${selectedConflictResolutionStrategy.name}`);
  }
}


const MAX_CYCLES = 100;
let cycle = 1;

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

run();

if (queries.length) {
  console.log(`Running ${queries.length} ${queries.length === 1?'query':'queries'}`);
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

if(justifications.length) {
  console.log(`The working memory consists of ${justifications.length} WMEs`);
  for (const {wme, justifications: j} of justifications) {
    let jStrings = [];
    for (const justification of j) {
      if('prod' in justification) {
        let productionJustification = justification as ProductionJustification;
        jStrings.push(`[${productionJustification.prod}:${productionJustification.token.toString()}]`);
      } else {
        jStrings.push('[Axiomatic]');
      }
    }
    console.log(`${wme.toString()}: ${jStrings.join(',')}`);
  }
}
