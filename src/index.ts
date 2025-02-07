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

interface Options extends CommandLineOptions{
  file: string,
  strategy: string,
  schemaCheck: boolean,
  interactive: boolean,
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

function interactiveHelp(prompt: string) {
  const request = prompt.trim();

  function showQuit() {
    console.log(' quit, exit, bye               Exit');
  }

  function showRetract() {
    console.log(' retract [str] [str] [str]     Retract axiomatic justification for WME ([str] [str] [str])');
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
  
- **Output Variables:** After the \`->\`, list the variables to output, separated by commas without additional parentheses or angle brackets.

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
  console.log(schemaDescription);
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
      const answer = await input({message: (openAiState.contextLength ? `[${openAiState.contextLength}]` : '') + '>'});
      if(!answer.trim()) {
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
