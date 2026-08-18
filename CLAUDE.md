# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

ReteReasoner is a single-file TypeScript CLI (`src/index.ts`, ~1300 lines) implementing a
forward-chaining production-rule reasoner on top of
[rete-next](https://github.com/dsouflis/rete-next), a sibling project — `node_modules/rete-next`
is symlinked to `../rete-next`. It reads a `.rete` production file, builds or loads a Rete network,
runs it to a fixed point (or `MAX_CYCLES`), and optionally drops into an interactive REPL.

`README.md` already documents the domain/user-facing side in depth (CLI usage, interactive
commands, conflict resolution strategies, schema checking, fuzzy inference, session persistence) —
this file covers architecture and dev workflow instead of duplicating that.

## Commands

```bash
npm run dev -- -f <file.rete> [options]   # tsx --env-file=.env src/index.ts — run the CLI from TS source
npm run lint                               # eslint . (no eslint config file currently present in the repo)
npm test                                   # mocha, spec/**/*.spec.ts — no spec/ directory exists yet
npx tsc --noEmit                           # type-check only; there's no `compile`/`build` script
```

`-f`/`--file` (the default positional option) is required — running without it just prints the
usage banner and exits. `npm run dev` loads `.env` (`--env-file=.env`); `OPENAI_API_KEY` needs to be
set there for the interactive chatbot query flow (`interactiveChat`), but everything else works
without it.

There's no wired-up build step for normal use: `package.json`'s `main`/`types` point at `dist/`, but
`npm run dev` runs `src/index.ts` directly via `tsx`, and nothing runs `tsc` as part of the usual
workflow.

**Known environment quirk** (same root cause as in `rete-next`): in a WSL checkout that shares
`node_modules` with a Windows checkout of this repo, `tsx`'s bundled `esbuild` binary can be built
for the wrong platform (`@esbuild/win32-x64` present, `linux-x64` needed), and `npm run dev`/
`npm test` fail with a platform-mismatch error that has nothing to do with any code change.
Reinstalling `node_modules` from WSL would fix it locally but risks breaking the Windows-side
checkout that shares the same directory — verify those two commands from the Windows side instead.
`npx tsc --noEmit` works fine from either side, since it doesn't go through `tsx`/`esbuild`.

## Architecture

### Dependency on rete-next

Everything Rete-related — `Rete`, `Condition`/`GenericCondition`/`NegativeCondition`/
`PositiveCondition`/`AggregateCondition`, `Token`, `WME`/`FuzzyWME`, `ProductionNode`, the
condition-tree (de)serializer (`serializeCondition`/`deserializeCondition`), `evalVariablesInToken`
— comes from `rete-next/index`; the `.rete`-file grammar/parser (`parseRete`) comes from
`rete-next/productions0`. Since `rete-next`'s `package.json` has no `"exports"` map, these subpath
imports resolve straight to `rete-next`'s `.ts` source (via `tsx`'s loader, or TypeScript's own
resolution for `tsc`) — not to a `dist/` build. Changes made directly in `../rete-next/index.ts` are
picked up immediately here, no build step needed there.

### Module-level state

`src/index.ts` has no classes and no dependency injection — it's one flat module scope of mutable
state, declared near the top of the file, that every function below reads and writes directly:

- `rete: Rete` — the live matcher instance.
- `productions: ProductionSpec[]` — `{production: ProductionNode, rhsAssert?: GenericCondition[]}`.
  `rete-next` itself has no notion of an RHS *action*; `rhsAssert` (the facts to add when a
  production fires) is entirely this app's layer on top, tracked in parallel to `rete-next`'s own
  `ProductionNode`.
- `strata: ProductionSpec[][]` / `stratumBeingRead` — groups of productions separated by
  `#stratum` directives, used by the `stratifiedManual` conflict resolution strategy.
- `queries: Query[]`, `justifications: WMEJustification[]` — the query list, and the
  justification-based truth-maintenance structure (`ProductionJustification`/
  `DefuzzificationJustification`/`AxiomaticJustification`) that `retract`/`explain` operate on.
- `patternsForAttributes`, `schemaCheck` — the `#schema`/`#schemacheck` machinery.
- `fuzzySystem`, `fuzzyVariableKinds` — fuzzy inference config from `#fuzzy` directives
  (`DeclaredFuzzyVariable` implements rete-next's `FuzzyVariable`; `MinMaxFuzzySystem`/
  `MultiplicativeFuzzySystem` implement `FuzzySystem`).

### Parsing and execution

`readInputInterpretDirectivesAndParseAndExecute` walks the input file line by line, splitting off
`#`-prefixed directive lines (handled by `executeDirective`/`fuzzyDirectiveHandling`, which mutate
the module state above) from Rete syntax, which gets batched and handed to `parseAndExecute`
(parses via `parseRete`, then calls `rete.addProduction`/`rete.addWMEsFromConditions`/`rete.query`
per parsed spec). This path runs for a fresh start — no saved session, or `-l`/`--clean` passed.

### Run loop and conflict resolution

`run()` loops: compute the conflict set (`findConflictSet`), pick one candidate via the selected
`conflictResolutionStrategy` (`firstMatchConflictResolution` / `stratifiedManual`, chosen by
`-s`/`--strategy`), fire it (`willFire()` on the `ProductionNode`, then update `justifications` and
call `rete.addWMEsFromConditions` for its `rhsAssert`), repeat until no conflicts remain or
`MAX_CYCLES` is hit. `--reactive` switches to a TMS-free mode where RHS WMEs toggle (add/remove) on
repeated assertion instead of accumulating justifications.

### Session persistence (save/load)

Every run ends by writing the whole session to `<basename>.json` next to the input file
(`saveSession`) — `rete.exportNetwork()` (rete-next's network snapshot; see
`../rete-next/README-snapshot.md`) plus everything layered on top here (`justifications`,
`rhsAssert` per production, `queries`, `strata`, schema/fuzzy config). On startup, if that file
exists and `-l`/`--clean` wasn't passed, `loadSession` restores everything from it instead of
parsing the `.rete` file at all — `restoreNetwork` rebuilds the network structure and bulk-loads its
content without replaying any WMEs through the matcher. `WME`/`Token` references inside
`justifications` are re-resolved *by value* against the restored network
(`WME.toString()`/`Token.toArray()`), not through any rete-next-side index — that correlation logic
lives entirely in `serializeJustification`/`deserializeJustification` here. See `README.md`'s
"Session Persistence" section for the user-facing behavior and the exact `-l`/`--clean` semantics,
and `TESTING-session-save-load.md` (untracked, local) for a manual test checklist — this feature has
not yet been exercised end to end.

### Interactive mode

`interactive()` is a REPL (`@inquirer/prompts`) dispatching on `retract`/`explain`/`run`/`clear`/
`help`/`quit`|`exit`|`bye`, falling through to `interactiveChat` (OpenAI-backed natural-language
query support, gated on `OPENAI_API_KEY` and on the knowledge base's `#schema` documentation) for
anything else.
