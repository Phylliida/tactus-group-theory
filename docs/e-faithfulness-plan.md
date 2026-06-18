# Obligation E (faithfulness) — full arc plan

The backward/⟹ direction of Theorem 1, the last hard obligation. Foundation already done:
**property (i) — config-basis injectivity (T-free) — COMPLETE** (`lemma_canw_eval_nontrivial`,
brick 108). Source: Aanderaa–Cohen §2 (paper in repo, text at /tmp/ac_paper.txt lines ~164–255).

## The factoring of E

```
[k, t(α,β)] = 1
   ──(III)──▶  t(α,β) ∈ ⟨t, rᵢ, lⱼ⟩            (k commutes ⟺ in the k-associated subgroup)
   ──(vii)──▶  t(α,β) ∈ ⟨T(M), rᵢ, lⱼ⟩          (⟨t,rᵢ,lⱼ⟩ = ⟨T(M),rᵢ,lⱼ⟩)
   ──(vi)───▶  t(α,β) ∈ A ∩ ⟨T(M),rᵢ,lⱼ⟩ = T(M)  (the subgroup-intersection collapse)
   ──(i)────▶  (α,β) ∈ H₀(M)                     (T-free: T(M)=⟨t(a,b):(a,b)∈H₀⟩, basis distinct) ✓
```
where `T(M) = ⟨ t(a,b) : (a,b) ∈ H₀(M) ⟩` and `t = t(0,0) ∈ T(M)` since `(0,0)∈H₀`.

## The two general HNN/Britton engines (un-built — build on `britton_lemma_full`)

**Property (III)** (paper line 201): in `HNN(H, p; p⁻¹Ap=A)` with the *identity* iso, `p⁻¹hp = h`
(h∈H) ⟹ `h ∈ A`.  *Proof:* the word `p⁻¹hp h⁻¹` is trivial; if `p` occurs it must pinch
(Britton), and a `p`-pinch here forces `h ∈ A`. **Use:** the k-extension `G(M)=HNN(B(M),k;
identity on ⟨t,rᵢ,lⱼ⟩)`, giving `[k,t(α,β)]=1 ⟹ t(α,β)∈⟨t,rᵢ,lⱼ⟩`. Difficulty: **moderate**
(single HNN over B(M); a direct Britton-pinch consequence).

**Property (II)** (paper line 191) — *the engine of (vi)*: if `K ≤ H` with `φᵢ(K∩Aᵢ)=K∩A₋ᵢ`
for all i, then `H ∩ ⟨K, pᵢ⟩ = K`.  *Proof:* a `⟨K,pᵢ⟩`-word — pinches **preserve** `⟨K,pᵢ⟩`
membership (the φ condition ensures the pinched element stays in the subgroup); so any element
of `⟨K,pᵢ⟩` has a pinch-free representative; by Britton, a pinch-free word with any `pᵢ` is **not
in H**; so if it's in H it has no `pᵢ`, i.e. it's in `K`. Difficulty: **moderate–hard** (the
deepest general lemma; pinch-preservation + pinch-free-implies-no-stable). This is what's missing
from `britton_via_tower` and the main new infrastructure.

## The specific subgroup characterizations

**Property (ii)** (line 209): `T ∩ ⟨t(i,j), xᵐ, yᵐ⟩` has basis `{t(r,s) : r≡i, s≡j (mod m)}`.
- ⊇ (CONCRETE first brick): `t(r,s) = (yᵐ)⁻ᵇ(xᵐ)⁻ᵃ · t(i,j) · (xᵐ)ᵃ(yᵐ)ᵇ` for `r=i+am, s=j+bm`
  — a conjugation identity (exhibit the `in_generated_subgroup` factors). Like the forward-step
  conjugations already done.
- ⊆ (harder): any element of `⟨t(i,j),xᵐ,yᵐ⟩` is `u·xᵃᵐ·yᵇᵐ` with `u ∈ ⟨t(r,s):r≡i,s≡j⟩`; intersect
  with T (the t-part) ⟹ the basis. Uses A's structure as `HNN(⟨t,x⟩, y)` / free-product normal form.

**Properties (iii),(iv),(v)** (lines 218–232): the subgroups `⟨t(i,j),xᵐ,yᵐ⟩` are conjugates of
`⟨t,xᵐ,yᵐ⟩≅A` hence mutually isomorphic (iii); the generator-map induces isos of the subgroups AND
of their T-intersections (iv); and for a quadruple, `T(M)∩⟨t(a,b),xᵐ,yᵐ⟩ ≅ T(M)∩⟨t(c,0),xᵐ²,y⟩`
because the iso sends `t(a,b)↦t(a',b')` with `(a,b)→(a',b')`, and `(a,b)∈H₀ ⟺ (a',b')∈H₀` (v).
Difficulty: **moderate** (rest on (ii) + the forward step, which is done).

## Assembly

**Property (vii)** (line 234): `⟨T(M),rᵢ,lⱼ⟩ = ⟨t,rᵢ,lⱼ⟩`. `⊇`: `t=t(0,0)∈T(M)`. `⊆`: each
`t(a,b), (a,b)∈H₀`, is in `⟨t,rᵢ,lⱼ⟩` by the **forward membership induction** (`r⁻¹t(a,b)r=t(a',b')`
+ induction on the computation; we have the forward step `lemma_forward_step_*_tower` and the ⟸
induction `lemma_reaches_implies_k_commutes` — extract/mirror the membership form). Difficulty: moderate.

**Property (vi)** (line 233): `A ∩ ⟨T(M),rᵢ,lⱼ⟩ = T(M)`, by **property (II)** with `K=T(M)`,
`pᵢ=rᵢ,lⱼ`, the φ-condition being **property (v)**. Difficulty: moderate (apply II + v).

**E**: chain III → vii → vi → (i). **F (Theorem 1)**: `[k,t(α,β)]=1 ⟺ (α,β)∈H₀(M)` — combine E
(⟹) with the proven ⟸ (`lemma_reaches_implies_k_commutes`). Difficulty: moderate (assembly).

## Brick sequence (proposed)

1. **(ii)⊇** — conjugation identity (concrete warm-up; exercises `in_generated_subgroup` membership).
2. **(III)** — k-commutation ⟹ membership (first real Britton-consequence; unblocks the top of E).
3. **(II)** — the general HNN subgroup-intersection engine (the deep new infrastructure).
4. **(ii)⊆** + **(iii),(iv),(v)** — the subgroup characterizations + machine-step condition.
5. **(vii)**, **(vi)** — assembly of the intersection collapse.
6. **E**, then **F** — the faithfulness and Theorem 1.

## What's pre-built vs new

- **Pre-built:** `britton_lemma_full` (the tower Britton's lemma), `has_pinch`/`has_pinch_at`,
  `in_generated_subgroup` (benign.rs), the whole config/B(M)/G(M) construction, the forward steps,
  config-basis injectivity (i), the ⟸ direction.
- **New (the work):** property (III), property (II) [engine], property (ii) both directions,
  (iii)–(vii), E, F. ~6–8 major bricks, each moderate→hard, all canonical (no dragons).

## Risks / notes

- **Property (II) is the crux** of this arc — the pinch-preservation argument over the B(M) tower
  (multi-stable-letter rᵢ,lⱼ). May need a tower-level statement (preserve membership through each
  HNN level). Scout `britton_via_tower` for pinch-out / pinch-preservation helpers before building.
- Subgroup membership (`in_generated_subgroup`) ⊆-reasoning is a *different flavor* than the
  word-nontriviality we've done — expect new helper lemmas (membership closure under product/inverse,
  conjugation-into-subgroup, intersection characterization).
- Keep faithful to the property-(I)–(vii) structure; the paper's proof is the canonical route.
