# ReteReasoner
ReteReasoner is a bare-bones forward-inference reasoner based on  [rete-next](https://github.com/dsouflis/rete-next),
another project of mine that implements a Rete engine.

## Usage
```
Options
  -f, --file           File with Rete productions
  -s, --strategy       Conflict resolution strategy [optional]
  -c, --schema-check   Enable schema check before reading file [optional]
  -i, --interactive    Launch interactive session after running [optional]
  -t, --trace          Enable tracing [optional]  
```
Option `-f` is the default option so one can specify the file directly.

### Input File
The input file consists of directives (starting with `#`), asserts, productions and queries. Directives, asserts and productions are executed as they are read.
Queries are executed after running the system. 

## Running
Running the system cycles until the system converges into a stable state, or if a maximum number of cycles is reached.

### Conflict Resolution Strategy Argument
The optional argument after the input file path is used to select a Conflict Resolution Strategy (see below).
The first strategy that matches the argument as a (case-insensitive) prefix is selected.

## Truth Maintenance
The reasoner uses a justification-based truth maintenance system, with a similar concept as the demonstration
in rete-next. Cycles are not detected by this implementation, which can lead to cycles
(but see "Stratified Conflict Detection Strategy" on a way to work around this to implement
default logic).

## Conflict Resolution Strategies
In each cycle, the conflict set is computed and a conflict resolution strategy is invoked to select which
candidate production will file. The default strategy is "matchFirst", which selects the first one in file
reading order. This strategy is sufficient for all rulesets that have well-defined semantics: those that 
don't use negation and aggregates. These converge to the same fixed-point state, which does not depend on the 
order of productions. A solution to cope with rules that are interdependent in a way that their order of firing
produces a different stable state, is to *stratify* the rules (see below).

An example of an input file to use with the default strategy, is [test.rete](./test.rete).

### Stratified (Manual) Strategy
The only other strategy currently implemented is the "stratifiedManual" strategy. It relies on separating productions
with the `#stratum` directive. Conflict resolution starts at the first stratum and, every time no production in a stratum 
is found to be eligible, the stratum is abandoned and conflict resolution proceeds with the subsequent strata.

An example of an input file to use with this strategy, is [test2.rete](./test2.rete). Let's examine how this
strategy can help implementing *default logic*. Suppose we want to implement the rule that, in the absense of
information to the contrary, a bird is supposed to be able to fly.

Suppose we have three species. Ducks, which can fly, dodos, which cannot, and robbins, for which we don't know one 
way or the other.

```
(!  (duck is-a bird)
    (robbin is-a bird)
    (dodo is-a bird)
)

(!  (duck fly can)
    (dodo fly cannot)
)
```

A straightforward way one could think of implementing this is with the following rule:

```
(   (<species> is-a bird)
    -{(<species> fly <_>)}
-> "Default values"
    (!
        (<species> fly can)
    )
)
```

This rule would work in a "reactive" implementation of a production system, and rete-next can be used to implement one
without a problem. But in the context of a reasoner that implements some form of Truth Maintenance, this rule results
in infinite cycles, which can be seen if one runs [test2-fail.rete](./test2-fail.rete):
```
Cycle 1
Default values
Cycle 2
Default values
No justifications left, will be removed: (robbin fly can)
Cycle 3
Default values
Cycle 4
Default values
No justifications left, will be removed: (robbin fly can)
...... and so on ......
```

Because adding `(robbin fly can)` invalidates the condition `-{(<species> fly <_>)}` for `<species>`=robin, so
the token from the production in this cycle is invalidated and the fact `(robbin fly can)` is removed in the next.

To work around that, we use the Stratified (Manual) strategy on file [test2.rete](./test2.rete). Two rules are used,
in two consecutive strata, and the actual logic which uses default values, lies in a subsequent stratum:

```
(   (<species> is-a bird)
    -{(<species> fly <_>)}
-> "1. Default values prepare"
    (!
        (<species> fly-prepare can)
    )
)
#stratum
(   (<species> fly-prepare can)
-> "2. Default values commit"
    (!
        (<species> fly can)
    )
)
#stratum
(   (<species> fly can)
-> "3. Hunting possibility by shooting"
    (!
        (<species> hunting-possible-by shooting)
    )
)

(   (<species> fly cannot)
-> "3. Hunting possibility by shooting or chasing"
    (!  (<species> hunting-possible-by shooting)
        (<species> hunting-possible-by chasing)
    )
)
```

What do we gain with that? Adding the fact `(robbin fly can)` does invalidate the token of production "1. Default values
prepare", like before, but that fact is added by "2. Default values commit" in stratum #2 while "1. Default values prepare" 
is in stratum #1, which we have already left behind. It is still a logical inconsistency, but we have striken a balance 
between maintaining logical consistency and "anything goes". 

### Stratified (Automatic) Strategy
This is not yet implemented. The idea is to find the dependencies among rules and break them up in strata 
automatically.

## Schema Checking
The directive `#schema` can be used to define allowed patterns of facts and conditions. These serve as plain comments,
unless schema checking is enabled with the directive `#schemacheck on`. It can be disabled with `#schemacheck off` and
only facts and rules that are in sections of the file where schema checking is on are checked. Check failure just
produces warnings. It does not stop execution of the ruleset.

Example from [test2.rete](./test2.rete):

```
#schema _ is-a _
#schema _ fly can
#schema _ fly cannot
#schema _ fly-prepare can
#schema _ hunting-possible-by shooting
#schema _ hunting-possible-by chasing
```

This set of directives means that only the following attributes are accepted: 
- Attribute `is-a` does not constrain its id and value.
- Attribute `fly` only accepts `can` and `cannot` as values.
- Attribute `fly-prepare` only accepts `can` as a value.
- Attribute `hunting-possible-by` only accepts `shooting` and `chasing` as values.

You can see an example of warnings if you run [schema-fail.rete](./schema-fail.rete). Examine the schema patterns
and witness how the system warns of the following:

```
No schema registered for attribute is-a
No schema pattern matches WME (duck fly canitreally)
No schema pattern matches condition (<species> fly-prepare itcan)
```

## Interactive operation
One can request an interactive shell after the execution of the file. The commands supported are:

```
Commands
 quit, exit, bye               Exit
 retract [str] [str] [str]     Retract axiomatic justification for WME ([str] [str] [str])
 run [clauses]                 Run the clauses provided
 clear                         Reset the chat and start over
 [Prompt to chatbot]           Chat with ChatGPT
```

### Retract
"Retract" takes three arguments, as in:

```
√ > retract Sarah mother Isaac
```
Only WMEs with an axiomatic justifications can be specified. This retracts the axiomatic justification for the
corresponding WME. If no other justification exists, the WME is removed from the working memory, and a new stable state
of the knowledge base is computed. 

### Run
"Run" is straightforward. It executes the clauses provided and a new stable state of the knowledge base is computed. 

### Chatting with the knowledge base
One can chat with the knowledge base, with the prerequisite that the OPENAI_API_KEY env var must be set, and the
schema has been adequately been documented using `#schema` directives. Once can formulate queries for information and
the chatbot will ask for clarifications or propose Rete-next queries. The user is given the option to run them or not.
One can clear the chat with the "clear" command and start a new conversation.

### Fuzzy Inference
Rete-reasoner has a full implementation of fuzzy inference, built on top of the basic fuzzification operation in Rete-next. You
are advised to brush up [on the basic notions in the readme](https://github.com/dsouflis/rete-next/blob/main/README-fuzzy.md).
It is full integrated with the Truth Maintenance System.

Let us work on the included example, starting from the directives that define the fuzzy operations. Directive `#fuzzy` has
many forms that provide various configuration elements for fuzzy logic.
```
 #fuzzy [configuration]         Configure various aspects of the fuzzy operations

 system min-max|multiplicative
 Purpose: Configure what fuzzy system will be used. Options are "min-max" and "multiplicative"
 Example: #fuzzy system min-max

 Configuration elements:
 kind [variablekind] [fuzzy-value]:sigmoid [a] [c], [...more...]
 Purpose: Define a new kind of fuzzy variable. Currently, only the sigmoid function is supported
 Example: #fuzzy kind excellent-poor excellent:sigmoid 4 0.7, poor:sigmoid -4, 0.3

 var [variablename] [variablekind]
 Purpose: Define a fuzzy variable that is of a previously defined kind
 Example: #fuzzy var food excellent-poor
```
The first form is the `#fuzzy system` directive, that selects among two FuzzySystems. Min-max and Multiplicative. The
selection of Fuzzy System dictates how the conjuction of fuzzy membership values in a token (representing a 
conjunction of left-hand-side conditions) is computed, and how the disjunction of all justifications, from all rules
that have resulted in asserting a particular fuzzy variable, is computed to provide the crisp value for it.

The second form is the `#fuzzy kind` directive, that defines a new kind of fuzzy variable. Because Rete-next has a very
elementary implementation of defuzzification (as presented in the signature of `FuzzyVariable::computeValueForFuzzyMembershipValue`),
the fuzzy values that can be defined for the kind, can make sense only if they are two, representing the two opposite
sides. Or else there could not be a reversible fuzzification computation. For example, if there were values with "humpy"
membership functions, the fuzzy variable kind would not be reversible. This is an open avenue for development. Proper
defuzzification is done using function composition and some form of centroid computation to produce the crisp value.
However, it is still useful the way it is defined now.

The third form is the `#fuzzy var` directive, that introduces a new fuzzy variable of an already defined kind. The 
name of the variable is used as the attribute (middle value) of WMEs, in a dual role. On the one hand, there are 
WMEs of the form `(<id> attr <num>)` that encode crisp input and crisp output values. On the other hand, there are 
conditions and asserted FuzzyWMEs of the form `(<id> attr <fuzzy-value>)`.
