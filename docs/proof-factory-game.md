# The Proof Factory — a Factorio of proofs (design vision)

*The motivation behind this whole construction. Danielle's, "for fun" — captured from a
chat, 2026-06-12, the day the ⟸ direction of Theorem 1 closed.*

## The itch

Two braided motivations:

1. **Minimal emergent primitives.** ZFC carries a lot of baggage — first-order logic, the
   membership relation, and the axiom *schemas* (separation, replacement) that are secretly
   infinitely many axioms. A **finitely presented group whose word problem is ZFC-provable-
   equivalence** collapses all of that into: a finite bag of generators, a finite bag of
   relators, and **one operation** — multiply two words and reduce. "Is `σ↔τ` provable?"
   becomes "do these two strings multiply to the same group element?" The entire deductive
   apparatus of mathematics compiled down to *concatenate-and-cancel*. Whether the result is
   secretly clean or gloriously messy is itself the interesting open question. (Bet: the
   Aanderaa–Cohen/Higman route gives *messy* — `H₃` has a zoo of stable letters — but whether
   some far smaller presentation exists for ZFC-equivalence specifically feels genuinely open.)

2. **A game.** An open, base-building, *engineering* game — build-on-build-on-build — where the
   raw primitives are proofs. The group is what makes proof into a clean, conveyor-able material
   instead of a syntactic ritual.

## The core mapping (why the group makes a good game)

The relators **are** crafting recipes. A relator like `x·y·x⁻¹·y⁻¹ = 1` literally says "these
four chunks combine to nothing." A group presentation is a recipe book. So:

| Group / logic | Game |
|---|---|
| generators (`t, x, y`, stable letters, `c_j`, …) | **ores** — raw resources you mine |
| a word | **items / glyphs riding a belt** |
| the group operation (concatenate) | **the assembler** (shove two belts together) |
| a relator | **a crafting recipe** ("these chunks annihilate") |
| reduction (a relator-chunk cancels) | **a recipe firing** — glyphs cancel in a little puff |
| two words equal in the group | **the same item** (à la "300 iron + 100 copper *is* a circuit") |
| a **proof** | a **factory** that reduces a formula's word down to the identity (≈ *true*) |
| a **lemma** | a **saved blueprint** in your blueprint book |

**Win condition falls out for free:** "prove `1+1=2`" = "build the factory that makes the belt
carrying `f(1+1=2)` reduce, recipe by recipe, until nothing's left but the empty word." A proof
is a factory whose job is to cancel a thing down to silence. Build it, hit go, watch the symbols
eat themselves down to ∅.

## The killer mechanic: nested factory-buildings = abstraction itself

Lay out a mini-factory, confirm it works, then **collapse it into one opaque building** with just
input/output belts. That is not merely convenient — it *is* the mathematical act of abstraction,
exactly:

- the building's **interface** (which belts in, which out) = the **lemma's statement**
- its sealed **internals** = the **proof**
- **collapsing it** = the "prove once, never reopen, use as an atom" move (proof irrelevance / a
  derived rule of inference)

Late game you place a building labelled **"Peano Arithmetic"** with a thousand-tile factory folded
inside that you no longer remember building — the exact feeling of using a library you *could*
explain but never have to think about. The nesting absorbs the messiness instead of fighting it,
which is the sign it's the right core mechanic.

**This construction IS a worked example of that mechanic.** The Aanderaa–Cohen/Higman tower is
literally a stack of nested factory-buildings:

```
K_M  ──nest──▶  B(M)  ──nest──▶  G(M)  ──nest──▶  H₁  ──▶  H₂  ──▶  H₃
```

Each layer seals the previous one inside a building and adds one fresh generator-ore at the seam
(a stable letter that conjugates the machine within). The **"rope trick"** is the tooltip: *nest a
machine inside a building, add a rope (stable letter), pull.* Formalizing this group (see
`aanderaa-cohen-construction.md`, `higman-embedding-blueprint.md`) is, in effect, hand-assembling
the game's tutorial level.

## Goals, achievements, and one diabolical idea

- **Early game:** cancel single relators; build the basic numeral/successor machinery.
- **Mid-game megaproject:** prove `1+1=2` in ZFC — the full journey (∅ → successor `S(x)=x∪{x}`
  → the numerals → recursive `+` → the reduction). It's the *Principia Mathematica* meme rendered
  as a satisfying factory district with a ✓ PROVEN banner. Gamers know the meme; lean into it.
- **Open-problem achievements (the diabolical part):** list "Prove the Riemann Hypothesis,"
  Goldbach, twin primes, etc. as achievements. **The game is a sound verifier** — it only stamps ✓
  if the reduction actually reaches the identity. So *if a player ever earns the RH achievement,
  they have produced a real, formal, machine-checkable proof of RH.* Your idle base-builder is
  secretly a distributed theorem-mining rig wearing a Steam achievement as a lure. And one layer
  more cursed: RH might be **independent of ZFC**, so the achievement may be not just unimaginably
  hard but *literally unearnable* — and nobody, including the designer, can know which. An
  achievement whose attainability is itself an open problem in foundations.

## The honest catch (which is also the design gold)

The word problem for this group is **unsolvable** (Novikov–Boone — that's *why* it can carry ZFC).
So the game can **never auto-solve or auto-hint**: it can only *check* a completed factory (running
a reduction is decidable — execute the recipes, see if it hits identity), never *find* one for you.
"Easy to verify, impossible to autosolve" is precisely the engine that makes both Factorio and real
proof feel good. You are not handed the path. You build it, and you watch it work.

## The legibility fork (loops back to "messy or clean?")

The ores are the group's *encoding* generators (`t`, stable letters, `c_j`…), not friendly logical
atoms (∅, ∪, ¬, ∀). Building the game will reveal one of two outcomes:

- the raw generator-ores are weird-but-workable and players learn to think in them; **or**
- you want a friendly **logical-primitives layer** (∅, successor, ¬, ∧, ∀) that *compiles down* to
  generator-ore — in which case that friendly layer is itself just your first big nested
  factory-building.

Either way the nesting mechanic saves you. Which way it goes is the same "is the group secretly
clean?" curiosity that motivated the whole project.

---
*Status: vision only. The substrate (the f.p. ZFC group) is what's being formally built in
`machine_group.rs` and the `tactus-computability-theory` Higman chain. The game is downstream and
hypothetical — "dunno if it'll pan out, it's a curiosity I had for fun."*
