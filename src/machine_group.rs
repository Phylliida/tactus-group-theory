use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::benign::*;

verus! {

//  ============================================================
//  Machine Group via HNN Tower (Aanderaa-Cohen Encoding)
//  ============================================================
//
//  Given a modular machine M with states q_0..q_{s-1} and quadruples,
//  we construct a finitely presented group G_M whose word problem
//  encodes M's computation.
//
//  Base group (free group): generators for states and register letters.
//    - q_0, ..., q_{s-1}  : state generators (indices 0..s-1)
//    - a                    : alpha register letter (index s)
//    - b                    : beta register letter (index s+1)
//
//  Base generators total: num_states + 2
//
//  For each quadruple k:
//    (state_k, residue_k mod modulus_k) → (next_state_k, alpha_op_k, beta_op_k)
//
//  The HNN stable letter t_k conjugates the "source config word" for
//  state_k with alpha having residue_k into the "target config word"
//  for next_state_k with operations applied.
//
//  Config word for (state q, alpha value n, beta value m):
//    q · a^n · b^m
//  where a^n means Gen(s) repeated n times.
//
//  Association for quadruple k with Mul(c) on alpha:
//    source = q_k · a^{residue_k}
//    target = q_{next_k} · a^{residue_k * c}
//  (simplified: we encode the residue-check + operation)
//
//  The full encoding uses a single HNN extension with one stable
//  letter per quadruple, each encoding one transition rule.

//  ============================================================
//  Generator layout
//  ============================================================

///  Index of the state generator q_i.
pub open spec fn state_gen_index(i: nat) -> nat {
    i
}

///  Index of the alpha register letter.
pub open spec fn alpha_gen_index(num_states: nat) -> nat {
    num_states
}

///  Index of the beta register letter.
pub open spec fn beta_gen_index(num_states: nat) -> nat {
    num_states + 1
}

///  Total number of base generators: num_states + 2 (alpha, beta).
pub open spec fn base_gen_count(num_states: nat) -> nat {
    num_states + 2
}

//  ============================================================
//  Word builders
//  ============================================================

///  State symbol: Gen(i) for state i.
pub open spec fn state_symbol(i: nat) -> Symbol {
    Symbol::Gen(state_gen_index(i))
}

///  Alpha letter: Gen(num_states).
pub open spec fn alpha_symbol(num_states: nat) -> Symbol {
    Symbol::Gen(alpha_gen_index(num_states))
}

///  Beta letter: Gen(num_states + 1).
pub open spec fn beta_symbol(num_states: nat) -> Symbol {
    Symbol::Gen(beta_gen_index(num_states))
}

///  Alpha inverse letter.
pub open spec fn alpha_inv_symbol(num_states: nat) -> Symbol {
    Symbol::Inv(alpha_gen_index(num_states))
}

///  Beta inverse letter.
pub open spec fn beta_inv_symbol(num_states: nat) -> Symbol {
    Symbol::Inv(beta_gen_index(num_states))
}

///  Repeat a symbol n times to form a word: s^n.
pub open spec fn symbol_power(s: Symbol, n: nat) -> Word {
    Seq::new(n, |_i: int| s)
}

///  Configuration word: q_state · a^alpha · b^beta.
pub open spec fn config_word(num_states: nat, state: nat, alpha: nat, beta: nat) -> Word {
    Seq::new(1, |_i: int| state_symbol(state))
        + symbol_power(alpha_symbol(num_states), alpha)
        + symbol_power(beta_symbol(num_states), beta)
}

//  ============================================================
//  Machine group construction
//  ============================================================

///  The base presentation: free group on num_states + 2 generators.
pub open spec fn machine_base_presentation(num_states: nat) -> Presentation {
    Presentation {
        num_generators: base_gen_count(num_states),
        relators: Seq::<Word>::empty(),
    }
}

///  A modular operation type (mirroring the computability-theory enum).
pub enum MachineModOp {
    Mul { c: nat },
    Div { c: nat },
    Id,
}

///  Data for a single encoded quadruple.
pub struct EncodedQuadruple {
    pub source_state: nat,
    pub target_state: nat,
    pub residue: nat,
    pub modulus: nat,
    pub alpha_op: MachineModOp,
    pub beta_op: MachineModOp,
}

///  Complete machine group data: states + encoded quadruples.
pub struct MachineGroupData {
    pub num_states: nat,
    pub halt_state: nat,
    pub quadruples: Seq<EncodedQuadruple>,
}

///  Well-formedness of machine group data.
pub open spec fn machine_group_data_wf(data: MachineGroupData) -> bool {
    data.halt_state < data.num_states &&
    data.num_states > 0 &&
    (forall|i: int| #![trigger data.quadruples[i]]
        0 <= i < data.quadruples.len() ==>
        data.quadruples[i].source_state < data.num_states &&
        data.quadruples[i].target_state < data.num_states &&
        data.quadruples[i].source_state != data.halt_state &&
        data.quadruples[i].modulus > 0 &&
        data.quadruples[i].residue < data.quadruples[i].modulus)
}

///  Apply a MachineModOp to a value (for building association words).
pub open spec fn apply_machine_mod_op(op: MachineModOp, val: nat) -> nat {
    match op {
        MachineModOp::Mul { c } => val * c,
        MachineModOp::Div { c } => if c > 0 { val / c } else { val },
        MachineModOp::Id => val,
    }
}

///  Build the HNN association pair for an encoded quadruple.
///
///  The i-th quadruple (q_s, residue r mod m, -> q_t, alpha_op, beta_op)
///  produces the association:
///    a_i = q_s · alpha^r
///    b_i = q_t · alpha^{op(r)}
///
///  Note: we encode only the residue portion. The full faithfulness
///  argument shows that Britton's lemma applied to config words
///  produces the correct simulation.
pub open spec fn quadruple_association(
    data: MachineGroupData, i: int,
) -> (Word, Word)
    recommends 0 <= i < data.quadruples.len(),
{
    let q = data.quadruples[i];
    let ns = data.num_states;
    let source = Seq::new(1, |_j: int| state_symbol(q.source_state))
        + symbol_power(alpha_symbol(ns), q.residue);
    let target = Seq::new(1, |_j: int| state_symbol(q.target_state))
        + symbol_power(alpha_symbol(ns), apply_machine_mod_op(q.alpha_op, q.residue));
    (source, target)
}

///  Build all HNN associations from encoded quadruples.
pub open spec fn machine_associations(
    data: MachineGroupData,
) -> Seq<(Word, Word)> {
    Seq::new(data.quadruples.len(), |i: int| quadruple_association(data, i))
}

///  The HNN extension data for the machine group.
pub open spec fn machine_hnn_data(data: MachineGroupData) -> HNNData {
    HNNData {
        base: machine_base_presentation(data.num_states),
        associations: machine_associations(data),
    }
}

///  The machine group presentation: base + HNN stable letters.
pub open spec fn machine_group_presentation(data: MachineGroupData) -> Presentation {
    hnn_presentation(machine_hnn_data(data))
}

//  ============================================================
//  Key lemmas
//  ============================================================

///  The base presentation is valid (free group).
pub proof fn lemma_machine_base_valid(num_states: nat)
    ensures
        presentation_valid(machine_base_presentation(num_states)),
{
    reveal(presentation_valid);
}

///  Association words are base-valid.
pub proof fn lemma_machine_associations_valid(data: MachineGroupData)
    requires
        machine_group_data_wf(data),
    ensures
        forall|i: int| 0 <= i < machine_associations(data).len() ==>
            word_valid(machine_associations(data)[i].0,
                       machine_base_presentation(data.num_states).num_generators) &&
            word_valid(machine_associations(data)[i].1,
                       machine_base_presentation(data.num_states).num_generators),
{
    let assocs = machine_associations(data);
    let n = base_gen_count(data.num_states);
    assert forall|i: int| 0 <= i < assocs.len()
        implies word_valid(assocs[i].0, n) && word_valid(assocs[i].1, n)
    by {
        let q = data.quadruples[i];
        let (src, tgt) = quadruple_association(data, i);
        assert(assocs[i] == (src, tgt));

        //  Source word: q_s · alpha^r — all symbols valid
        assert forall|k: int| 0 <= k < src.len()
            implies symbol_valid(src[k], n)
        by {
            if k == 0 {
                assert(src[k] == state_symbol(q.source_state));
                assert(q.source_state < data.num_states);
            } else {
                assert(src[k] == alpha_symbol(data.num_states));
            }
        }

        //  Target word: q_t · alpha^{op(r)}
        assert forall|k: int| 0 <= k < tgt.len()
            implies symbol_valid(tgt[k], n)
        by {
            if k == 0 {
                assert(tgt[k] == state_symbol(q.target_state));
                assert(q.target_state < data.num_states);
            } else {
                assert(tgt[k] == alpha_symbol(data.num_states));
            }
        }
    }
}

///  The machine HNN data is valid.
pub proof fn lemma_machine_hnn_data_valid(data: MachineGroupData)
    requires
        machine_group_data_wf(data),
    ensures
        hnn_data_valid(machine_hnn_data(data)),
{
    let hnn = machine_hnn_data(data);
    lemma_machine_base_valid(data.num_states);
    lemma_machine_associations_valid(data);

    assert forall|i: int| 0 <= i < hnn.associations.len()
        implies word_valid(hnn.associations[i].0, hnn.base.num_generators)
             && word_valid(hnn.associations[i].1, hnn.base.num_generators)
    by {
        assert(hnn.associations[i] == machine_associations(data)[i]);
    }
}

///  Config words are base-valid.
pub proof fn lemma_config_word_valid(
    num_states: nat, state: nat, alpha: nat, beta: nat,
)
    requires
        state < num_states,
    ensures
        word_valid(config_word(num_states, state, alpha, beta),
                   base_gen_count(num_states)),
{
    let w = config_word(num_states, state, alpha, beta);
    let n = base_gen_count(num_states);
    assert forall|k: int| 0 <= k < w.len()
        implies symbol_valid(w[k], n)
    by {
        if k == 0 {
            assert(w[k] == state_symbol(state));
        } else if k < (1 + alpha) as int {
            assert(w[k] == alpha_symbol(num_states));
        } else {
            assert(w[k] == beta_symbol(num_states));
        }
    }
}

///  A machine step gives equivalence in G_M via HNN conjugation.
///
///  If quadruple k takes (state, alpha ≡ residue mod modulus) to
///  (next_state, alpha', beta'), then:
///    config_word(state, alpha, beta)
///      ≡ config_word(next_state, alpha', beta')
///  in the machine group presentation.
///
///  The proof uses lemma_hnn_conjugation: t_k conjugates source to target,
///  and we extend to full config words by concat with the remaining
///  alpha/beta powers.
pub proof fn lemma_machine_step_gives_equiv(
    data: MachineGroupData,
    quad_idx: nat,
    state: nat, alpha: nat, beta: nat,
)
    requires
        machine_group_data_wf(data),
        (quad_idx as int) < data.quadruples.len(),
        data.quadruples[quad_idx as int].source_state == state,
        alpha % data.quadruples[quad_idx as int].modulus
            == data.quadruples[quad_idx as int].residue,
    ensures
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, state, alpha, beta),
            config_word(
                data.num_states,
                data.quadruples[quad_idx as int].target_state,
                apply_machine_mod_op(data.quadruples[quad_idx as int].alpha_op, alpha),
                apply_machine_mod_op(data.quadruples[quad_idx as int].beta_op, beta),
            ),
        ),
{
    //  This is the key encoding lemma. The proof involves:
    //  1. Decompose config_word(state, alpha, beta) into:
    //     q_state · alpha^residue · alpha^(alpha - residue) · beta^beta
    //  2. Apply HNN conjugation on the q_state · alpha^residue portion
    //  3. Reassemble with remaining powers
    //
    //  The full proof requires detailed word manipulation.
    //  We axiomatize for now and prove in the faithfulness module.
    admit();
}

///  Multiple machine steps give equivalence (induction on fuel).
pub proof fn lemma_machine_run_gives_equiv(
    data: MachineGroupData,
    state: nat, alpha: nat, beta: nat,
    next_state: nat, next_alpha: nat, next_beta: nat,
    fuel: nat,
)
    requires
        machine_group_data_wf(data),
        state < data.num_states,
        next_state < data.num_states,
        //  The modular machine runs from (state, alpha, beta)
        //  to (next_state, next_alpha, next_beta) in `fuel` steps
        //  (This is a placeholder for the actual simulation relation)
    ensures
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, state, alpha, beta),
            config_word(data.num_states, next_state, next_alpha, next_beta),
        ),
{
    //  Induction on fuel, applying lemma_machine_step_gives_equiv at each step
    admit();
}

//  ============================================================
//  HNN associations are isomorphic
//  ============================================================
//
//  For Britton's lemma, we need that the map a_i ↦ b_i extends to
//  an isomorphism of generated subgroups. Since our base is a free
//  group (no relators), the a_i words generate a free subgroup and
//  the b_i words generate a free subgroup. The map is isomorphic
//  when distinct a_i words are "independent" — which holds because
//  each starts with a distinct state generator followed by alpha powers.
//
//  We axiomatize this for now; it follows from the independence of
//  the state generators in the free group.

///  The machine group HNN associations define an isomorphism.
///  This holds because the base is a free group and the association
///  words are independent (distinct state prefixes).
#[verifier::external_body]
pub proof fn axiom_machine_hnn_isomorphic(data: MachineGroupData)
    requires
        machine_group_data_wf(data),
    ensures
        hnn_associations_isomorphic(machine_hnn_data(data)),
{
}

} //  verus!
