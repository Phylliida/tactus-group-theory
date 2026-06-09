# The Aanderaa–Cohen machine group — exact construction (faithful to the source)

Source: S. Aanderaa & D. E. Cohen, *Modular machines, the word problem for finitely
presented groups and Collins' theorem*, Word Problems II (1980), pp. 1–16.
(PDF in `tactus-group-theory/`.) This replaces the broken stub `machine_group.rs`,
whose encoding was improvised and provably wrong.

## 1. Modular machine (config = a PAIR of naturals; state lives in the residues)

`M = (m, n, quadruples)`, `m > 1`, `0 < n < m`. Quadruples `(a,b,c,R)` and `(a,b,c,L)`
with `0 ≤ a,b < m`, `0 ≤ c < m²`, **at most one quadruple per residue pair `(a,b)`**.

- **Configuration** `(α,β) ∈ N²`. Write `α = u·m + a`, `β = v·m + b` (so `a = α mod m`,
  `b = β mod m`, `u = α div m`, `v = β div m`).
- `(α,β)` is **terminal** if no quadruple begins with `(a,b)`.
- **Transition** `(α,β) → (α',β')`:
  - quadruple `(a,b,c,R)`:  `α' = u·m² + c`,  `β' = v`.
  - quadruple `(a,b,c,L)`:  `α' = u`,        `β' = v·m² + c`.
- `H₀(M) = { (α,β) : (α,β) →* (0,0) }` when `(0,0)` is terminal (else `∅`). This is r.e.;
  it's the set realized in the word problem.

(NB: our `modular_machine.rs` is a *different variant* — explicit `state`, match on `α`-residue
only, Mul/Div by arbitrary constants. We adopt the **classic** machine above and will reduce
the ZFC register-machine enumerator to it.)

## 2. Base group and the config word (a CONJUGATE OF t — the stub's core error)

`A = ⟨ t, x, y | xy = yx ⟩  =  ⟨t⟩ * ⟨x,y | xy=yx⟩`.  (t is free; x,y commute; A is itself an
HNN extension of free `⟨t,x⟩` with stable letter `y`.)

**Config word:**  `t(r,s) := y⁻ˢ · x⁻ʳ · t · xʳ · yˢ`.

- `T := ⟨t⟩^A` (normal closure of t). `T` is **free with basis `{ t(r,s) }`** (property (i)).
- `T ∩ ⟨t(i,j), xᵐ, yᵐ⟩` has basis `{ t(r,s) : r≡i, s≡j (mod m) }` (property (ii)).

So a configuration `(α,β)` is the single group element `t(α,β)` — NOT `q_state·αᵅ·βᵝ`.

## 3. B(M): HNN extension of A, one stable letter per quadruple

```
B(M) = ⟨ A, rᵢ (i∈I), lⱼ (j∈J) |
   rᵢ⁻¹ t(aᵢ,bᵢ) rᵢ = t(cᵢ, 0),   rᵢ⁻¹ xᵐ rᵢ = xᵐ²,   rᵢ⁻¹ yᵐ rᵢ = y      (R-quadruple i)
   lⱼ⁻¹ t(aⱼ,bⱼ) lⱼ = t(0, cⱼ),    lⱼ⁻¹ xᵐ lⱼ = x,      lⱼ⁻¹ yᵐ lⱼ = yᵐ²    (L-quadruple j)
⟩
```
This is an HNN extension of A with stable letters `rᵢ, lⱼ` (validity via property (iii)).

**Forward / single step (the correct version of the stub's `lemma_machine_step_gives_equiv`):**
for an R-quadruple, the three relations telescope from the residue to the *full* config:
> `rᵢ⁻¹ · t(α,β) · rᵢ = t(α',β')`  whenever `(α,β) → (α',β')`.
Derivation: `t(um+a, vm+b) = y⁻ᵇ(yᵐ)⁻ᵛ x⁻ᵃ(xᵐ)⁻ᵘ t (xᵐ)ᵘxᵃ (yᵐ)ᵛyᵇ`; conjugate by `rᵢ` and apply
`xᵐ↦xᵐ²`, `yᵐ↦y`, `t(a,b)↦t(c,0)` ⇒ `t(um²+c, v) = t(α',β')`. (L symmetric.) **It is conjugation
by a stable letter, never bare equality** — the stub claimed bare equality and had no `t`/`y`/`x`
scaling, and dropped `β` entirely. That's the bug, named.

By induction on computation length: `t(α,β) ∈ ⟨t, rᵢ, lⱼ⟩` for `(α,β) ∈ H₀(M)`  (lines 238–243).

## 4. G(M): the finitely presented group, and the word-problem instance

```
G(M) = ⟨ B(M), k | k t = t k,  k rᵢ = rᵢ k,  k lⱼ = lⱼ k  (all i,j) ⟩
```
HNN extension of B(M) with stable letter `k` commuting with `t, rᵢ, lⱼ`. **Finitely presented.**

**Theorem 1 (the payoff):**
> `k · t(α,β) = t(α,β) · k`  in `G(M)`   ⟺   `t(α,β) ∈ ⟨t, rᵢ, lⱼ⟩`   ⟺   `(α,β) ∈ H₀(M)`.

- First `⟺` is HNN property (III): `k` commutes with `h` iff `h` lies in the associated
  subgroup `⟨t, rᵢ, lⱼ⟩`.
- Second `⟺` is the **faithfulness** — `T(M) = A ∩ ⟨t,rᵢ,lⱼ⟩ = ⟨t(α,β):(α,β)∈H₀(M)⟩`
  (properties (vi),(vii)) — proved via **the full force of Britton's Lemma** (paper §4).

So the word problem instance is the **commutator `[k, t(α,β)]`**, trivial iff the machine
drives `(α,β)` to `(0,0)`.

## Proof obligations (rebuild plan), all on our PROVEN Britton/HNN substrate

| # | Obligation | Difficulty |
|---|---|---|
| A | Define A, `t(r,s)`, B(M), G(M) faithfully (exact relators above) | mechanical |
| B | `T` free on `{t(r,s)}`; property (ii) | moderate (free-group/HNN) |
| C | **Forward:** `rᵢ⁻¹ t(α,β) rᵢ = t(α',β')` per step (the §3 telescoping) + induction | moderate |
| D | HNN validity of B(M), G(M) (property (iii)) | moderate |
| E | **Faithfulness (backward):** `t(α,β) ∈ ⟨t,rᵢ,lⱼ⟩ ⟹ (α,β) ∈ H₀(M)` via Britton §4 | **HARD — the crux** |
| F | Theorem 1: `[k,t(α,β)]=1 ⟺ (α,β)∈H₀(M)` | moderate (HNN prop III + E) |

## What this gives us, and the layer still above it

Theorem 1 realizes a **c.e. set** `H₀(M)` in a f.p. word problem. To embed the **CEER group**
`⟨gₙ | g_a g_b⁻¹ : a~b⟩` (so `f(σ)=f(τ) ⟺ ZFC⊢σ↔τ`) we need the **Higman embedding** layer that
sits on top — Aanderaa–Cohen's *following* paper (*…and the Higman–Clapham–Valiev embedding
theorem*) and the corresponding chapter of Cohen's *Combinatorial Group Theory: A Topological
Approach* (PDF in repo). TODO: read that layer and extend this doc with the embedding relators
before building past G(M).

## Chain to ZFC

`ZFC enumerator (register machine, PROVEN correct in tactus-computability-theory)` → reduce to a
**classic modular machine** `M` whose `H₀(M)` encodes the declared (ZFC-equivalent) pairs → `G(M)`
f.p. with `[k, t(code(a,b))]=1 ⟺ (a,b) declared` → Higman-embed the CEER group → explicit f.p.
group with `f(σ)=f(τ) ⟺ ZFC⊢σ↔τ`. Print it.
