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
in two consecutive strata:

```
(   (<species> is-a bird)
    -{(<species> fly <_>)}
-> "1. Default values prepare"
    (!
        (<species> fly-prepare can)
    )
)

(   (<species> fly-prepare can)
-> "2. Default values commit"
    (!
        (<species> fly can)
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
One can request an interactive shell after the execution of the file.

The only command supported yet is "retract" with three arguments, as in:

```
√ > retract Sarah mother Isaac
```
Only WMEs with an axiomatic justifications can be specified. This retracts the axiomatic justification for the
corresponding WME. If no other justification exists, the WME is removed from the working memory. 
