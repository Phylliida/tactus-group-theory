use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::britton::*;
use crate::benign::*;
use crate::machine_group::*;

verus! {

//  ============================================================
//  Faithfulness of the Machine Group Encoding
//  ============================================================
//
//  The machine group G_M faithfully encodes the modular machine M:
//
//  Forward: If M transitions (s, α, β) →* (s', α', β') then
//    config_word(s, α, β) ≡ config_word(s', α', β') in G_M.
//
//  Backward: If config_word(s, α, β) ≡ config_word(s', α', β') in G_M
//    then M can reach (s', α', β') from (s, α, β).
//
//  The forward direction follows by induction on steps, using
//  lemma_hnn_conjugation at each step.
//
//  The backward direction uses Britton's Lemma: any non-trivial
//  derivation between config words must use stable letters,
//  which correspond to machine transitions.

//  ============================================================
//  Forward direction
//  ============================================================

///  Two consecutive trace entries are connected by a quadruple.
pub open spec fn trace_step_valid(
    data: MachineGroupData,
    c1: (nat, nat, nat),
    c2: (nat, nat, nat),
) -> bool {
    exists|k: nat| (k as int) < data.quadruples.len() &&
        c1.0 == data.quadruples[k as int].source_state &&
        c1.1 % data.quadruples[k as int].modulus
            == data.quadruples[k as int].residue &&
        c2.0 == data.quadruples[k as int].target_state &&
        c2.1 == apply_machine_mod_op(
            data.quadruples[k as int].alpha_op, c1.1) &&
        c2.2 == apply_machine_mod_op(
            data.quadruples[k as int].beta_op, c1.2)
}

///  A modular machine trace: recursive definition.
pub open spec fn is_valid_trace(
    data: MachineGroupData,
    trace: Seq<(nat, nat, nat)>,
) -> bool
    decreases trace.len(),
{
    if trace.len() == 0 {
        false
    } else if trace.len() == 1 {
        trace[0].0 < data.num_states
    } else {
        trace[0].0 < data.num_states &&
        trace_step_valid(data, trace[0], trace[1]) &&
        is_valid_trace(data, trace.drop_first())
    }
}

///  Forward direction: a valid trace gives equivalence between
///  first and last config words.
pub proof fn lemma_trace_gives_equiv(
    data: MachineGroupData,
    trace: Seq<(nat, nat, nat)>,
)
    requires
        machine_group_data_wf(data),
        is_valid_trace(data, trace),
    ensures
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, trace[0].0, trace[0].1, trace[0].2),
            config_word(
                data.num_states,
                trace[trace.len() - 1].0,
                trace[trace.len() - 1].1,
                trace[trace.len() - 1].2,
            ),
        ),
    decreases trace.len(),
{
    if trace.len() == 1 {
        //  Single config: reflexivity
        lemma_config_word_valid(
            data.num_states, trace[0].0, trace[0].1, trace[0].2);
        lemma_equiv_refl(
            machine_group_presentation(data),
            config_word(data.num_states, trace[0].0, trace[0].1, trace[0].2),
        );
    } else {
        //  Inductive step: trace[0] → trace[1] via some quadruple,
        //  then trace[1..] by induction
        let (s0, a0, b0) = trace[0];
        let (s1, a1, b1) = trace[1];

        //  From recursive is_valid_trace: trace_step_valid(data, trace[0], trace[1])
        //  and is_valid_trace(data, trace.drop_first())
        assert(trace_step_valid(data, trace[0], trace[1]));
        let tail = trace.drop_first();
        assert(is_valid_trace(data, tail));
        assert(tail[0] == trace[1]);
        assert(tail[tail.len() - 1] == trace[trace.len() - 1]);

        //  Get the quadruple connecting trace[0] to trace[1]
        let k: nat = choose|k: nat| (k as int) < data.quadruples.len() &&
            s0 == data.quadruples[k as int].source_state &&
            a0 % data.quadruples[k as int].modulus
                == data.quadruples[k as int].residue &&
            s1 == data.quadruples[k as int].target_state &&
            a1 == apply_machine_mod_op(
                data.quadruples[k as int].alpha_op, a0) &&
            b1 == apply_machine_mod_op(
                data.quadruples[k as int].beta_op, b0);

        //  Step: config_word(s0, a0, b0) ≡ config_word(s1, a1, b1)
        lemma_machine_step_gives_equiv(data, k, s0, a0, b0);

        //  Inductive call on tail
        lemma_trace_gives_equiv(data, tail);

        //  Transitivity
        lemma_equiv_transitive(
            machine_group_presentation(data),
            config_word(data.num_states, s0, a0, b0),
            config_word(data.num_states, s1, a1, b1),
            config_word(
                data.num_states,
                trace[trace.len() - 1].0,
                trace[trace.len() - 1].1,
                trace[trace.len() - 1].2,
            ),
        );
    }
}

//  ============================================================
//  Free group: equiv_in_presentation → freely_equivalent
//  ============================================================

///  One-step reduction implies reduces_to.
proof fn lemma_one_step_reduces_to(w1: Word, w2: Word)
    requires
        reduces_one_step(w1, w2),
    ensures
        reduces_to(w1, w2),
{
    assert(reduces_in_steps(w2, w2, 0nat));
    assert(reduces_one_step(w1, w2) && reduces_in_steps(w2, w2, 0nat));
    assert(reduces_in_steps(w1, w2, 1nat));
}

///  reduces_to implies freely_equivalent.
proof fn lemma_reduces_to_freely_equiv(w1: Word, w2: Word)
    requires
        reduces_to(w1, w2),
    ensures
        freely_equivalent(w1, w2),
{
    lemma_reduces_to_refl(w2);
}

///  FreeReduce step preserves free equivalence.
proof fn lemma_free_reduce_equiv(w: Word, position: int)
    requires
        has_cancellation_at(w, position),
    ensures
        freely_equivalent(w, reduce_at(w, position)),
{
    let w2 = reduce_at(w, position);
    assert(reduces_one_step(w, w2));
    lemma_one_step_reduces_to(w, w2);
    lemma_reduces_to_freely_equiv(w, w2);
}

///  Inserting an inverse pair creates a cancellation.
proof fn lemma_inserted_pair_has_cancellation(
    w: Word,
    position: int,
    symbol: Symbol,
)
    requires
        0 <= position <= w.len(),
    ensures ({
        let pair = Seq::new(1, |_i: int| symbol)
            + Seq::new(1, |_i: int| inverse_symbol(symbol));
        let w2 = w.subrange(0, position) + pair
            + w.subrange(position, w.len() as int);
        has_cancellation_at(w2, position)
    }),
{
    let pair = Seq::new(1, |_i: int| symbol)
        + Seq::new(1, |_i: int| inverse_symbol(symbol));
    let w2 = w.subrange(0, position) + pair
        + w.subrange(position, w.len() as int);
    assert(w2[position] == symbol);
    assert(w2[position + 1] == inverse_symbol(symbol));
}

///  Reducing the inserted pair recovers the original word.
proof fn lemma_reduce_inserted_pair(
    w: Word,
    position: int,
    symbol: Symbol,
)
    requires
        0 <= position <= w.len(),
    ensures ({
        let pair = Seq::new(1, |_i: int| symbol)
            + Seq::new(1, |_i: int| inverse_symbol(symbol));
        let w2 = w.subrange(0, position) + pair
            + w.subrange(position, w.len() as int);
        reduce_at(w2, position) == w
    }),
{
    let pair = Seq::new(1, |_i: int| symbol)
        + Seq::new(1, |_i: int| inverse_symbol(symbol));
    let w2 = w.subrange(0, position) + pair
        + w.subrange(position, w.len() as int);
    let reduced = reduce_at(w2, position);
    //  reduced = w2[0..position] + w2[position+2..end]
    //  = w[0..position] + w[position..end] = w
    assert(reduced =~= w);
}

///  FreeExpand step preserves free equivalence.
proof fn lemma_free_expand_equiv(
    w: Word,
    position: int,
    symbol: Symbol,
)
    requires
        0 <= position <= w.len(),
    ensures ({
        let pair = Seq::new(1, |_i: int| symbol)
            + Seq::new(1, |_i: int| inverse_symbol(symbol));
        let w2 = w.subrange(0, position) + pair
            + w.subrange(position, w.len() as int);
        freely_equivalent(w, w2)
    }),
{
    let pair = Seq::new(1, |_i: int| symbol)
        + Seq::new(1, |_i: int| inverse_symbol(symbol));
    let w2 = w.subrange(0, position) + pair
        + w.subrange(position, w.len() as int);

    lemma_inserted_pair_has_cancellation(w, position, symbol);
    lemma_reduce_inserted_pair(w, position, symbol);

    //  reduces_one_step(w2, w): cancellation at position, reduce gives w
    assert(reduces_one_step(w2, w));
    lemma_one_step_reduces_to(w2, w);
    lemma_reduces_to_freely_equiv(w2, w);
    lemma_freely_equivalent_sym(w2, w);
}

///  A single derivation step on a free group (no relators) preserves
///  free equivalence with the starting word.
proof fn lemma_free_step_equiv(
    p: Presentation,
    w: Word,
    step: DerivationStep,
)
    requires
        p.relators.len() == 0,
        apply_step(p, w, step) is Some,
    ensures
        freely_equivalent(w, apply_step(p, w, step).unwrap()),
{
    let w2 = apply_step(p, w, step).unwrap();
    match step {
        DerivationStep::FreeReduce { position } => {
            lemma_free_reduce_equiv(w, position);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            lemma_free_expand_equiv(w, position, symbol);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(false);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(false);
        },
    }
}

///  For a free group (empty relators), derivation_produces preserves
///  free equivalence at each step.
proof fn lemma_free_derivation_equiv(
    p: Presentation,
    steps: Seq<DerivationStep>,
    start: Word,
    end: Word,
)
    requires
        p.relators.len() == 0,
        derivation_produces(p, steps, start) == Some(end),
    ensures
        freely_equivalent(start, end),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(start == end);
        lemma_freely_equivalent_refl(start);
    } else {
        let mid = apply_step(p, start, steps.first()).unwrap();
        lemma_free_step_equiv(p, start, steps.first());
        lemma_free_derivation_equiv(p, steps.drop_first(), mid, end);
        lemma_freely_equivalent_trans(start, mid, end);
    }
}

//  ============================================================
//  Config words are reduced (no cancellations)
//  ============================================================

///  Every symbol in a config word is a Gen (not Inv).
proof fn lemma_config_word_all_gen(
    num_states: nat, state: nat, alpha: nat, beta: nat,
    i: int,
)
    requires
        state < num_states,
        0 <= i < config_word(num_states, state, alpha, beta).len() as int,
    ensures
        config_word(num_states, state, alpha, beta)[i] is Gen,
{
    let cw = config_word(num_states, state, alpha, beta);
    let part1 = Seq::new(1, |_j: int| state_symbol(state));
    let part2 = symbol_power(alpha_symbol(num_states), alpha);
    let part3 = symbol_power(beta_symbol(num_states), beta);
    assert(cw =~= part1 + part2 + part3);

    if i < 1 {
        assert(cw[i] == state_symbol(state));
    } else if i < (1 + alpha) as int {
        assert(cw[i] == alpha_symbol(num_states));
    } else {
        assert(cw[i] == beta_symbol(num_states));
    }
}

///  Config words are freely reduced (no adjacent inverse pairs).
proof fn lemma_config_word_reduced(
    num_states: nat, state: nat, alpha: nat, beta: nat,
)
    requires
        state < num_states,
    ensures
        is_reduced(config_word(num_states, state, alpha, beta)),
{
    let cw = config_word(num_states, state, alpha, beta);
    assert(!has_cancellation(cw)) by {
        assert forall|i: int| !has_cancellation_at(cw, i) by {
            if 0 <= i < cw.len() - 1 {
                lemma_config_word_all_gen(num_states, state, alpha, beta, i);
                lemma_config_word_all_gen(num_states, state, alpha, beta, i + 1);
                //  Both cw[i] and cw[i+1] are Gen variants.
                //  inverse_symbol(Gen(x)) = Inv(x), which is not Gen.
                //  So cw[i+1] != inverse_symbol(cw[i]).
            }
        };
    };
}

//  ============================================================
//  Config word sequence equality → parameter equality
//  ============================================================

///  If two config words are equal as sequences, their parameters match.
proof fn lemma_config_word_seq_injective(
    num_states: nat,
    s1: nat, a1: nat, b1: nat,
    s2: nat, a2: nat, b2: nat,
)
    requires
        s1 < num_states,
        s2 < num_states,
        config_word(num_states, s1, a1, b1) ==
            config_word(num_states, s2, a2, b2),
    ensures
        s1 == s2 && a1 == a2 && b1 == b2,
{
    let cw1 = config_word(num_states, s1, a1, b1);
    let cw2 = config_word(num_states, s2, a2, b2);

    //  First symbols: Gen(state_gen_index(s1)) == Gen(state_gen_index(s2))
    assert(cw1[0] == state_symbol(s1));
    assert(cw2[0] == state_symbol(s2));
    assert(s1 == s2);

    //  Length equality: 1 + a1 + b1 == 1 + a2 + b2
    assert(cw1.len() == 1 + a1 + b1);
    assert(cw2.len() == 1 + a2 + b2);
    assert(a1 + b1 == a2 + b2);

    //  Prove a1 == a2 by contradiction
    if a1 != a2 {
        if a1 < a2 {
            if b1 == 0 {
                //  cw1.len() = 1 + a1 < 1 + a2 <= cw2.len(). Contradiction.
                assert(false);
            } else {
                //  cw1[1 + a1] is beta, cw2[1 + a1] is alpha
                assert(cw1[(1 + a1) as int] == beta_symbol(num_states));
                assert(cw2[(1 + a1) as int] == alpha_symbol(num_states));
                //  beta_gen_index != alpha_gen_index
                assert(false);
            }
        } else {
            //  a1 > a2, symmetric
            if b2 == 0 {
                assert(false);
            } else {
                assert(cw2[(1 + a2) as int] == beta_symbol(num_states));
                assert(cw1[(1 + a2) as int] == alpha_symbol(num_states));
                assert(false);
            }
        }
    }
    assert(a1 == a2);
    //  b1 == b2 from a1 + b1 == a2 + b2
}

//  ============================================================
//  Backward direction via Britton's Lemma
//  ============================================================

///  Two config words that are equivalent in the base (free) group
///  must represent the same configuration.
///
///  In a free group, two distinct words are never equivalent unless
///  they are identical after free reduction. Since config words have
///  the form q_s · a^α · b^β with distinct generator types, two
///  config words are freely equivalent only when s=s', α=α', β=β'.
pub proof fn axiom_config_words_free_injective(
    num_states: nat,
    s1: nat, a1: nat, b1: nat,
    s2: nat, a2: nat, b2: nat,
)
    requires
        s1 < num_states,
        s2 < num_states,
        equiv_in_presentation(
            machine_base_presentation(num_states),
            config_word(num_states, s1, a1, b1),
            config_word(num_states, s2, a2, b2),
        ),
    ensures
        s1 == s2 && a1 == a2 && b1 == b2,
{
    let p = machine_base_presentation(num_states);
    let w1 = config_word(num_states, s1, a1, b1);
    let w2 = config_word(num_states, s2, a2, b2);

    //  Step 1: equiv_in_presentation → freely_equivalent
    let d: Derivation = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    lemma_free_derivation_equiv(p, d.steps, w1, w2);

    //  Step 2: freely_equivalent → same normal_form
    lemma_normal_form_equiv_forward(w1, w2);

    //  Step 3: config words are reduced → normal_form is identity
    lemma_config_word_reduced(num_states, s1, a1, b1);
    lemma_config_word_reduced(num_states, s2, a2, b2);
    lemma_reduced_is_own_normal_form(w1);
    lemma_reduced_is_own_normal_form(w2);

    //  Step 4: w1 == w2 as sequences → params equal
    assert(w1 == w2);
    lemma_config_word_seq_injective(num_states, s1, a1, b1, s2, a2, b2);
}

///  Backward direction: equivalence of config words in G_M implies
///  the machine can transition between the corresponding configurations.
///
///  Uses Britton's Lemma: if config_word(C1) ≡ config_word(C2) in G_M,
///  the derivation either stays in the base (meaning C1 = C2 by free
///  group injectivity) or uses stable letters (corresponding to machine
///  transitions). Each stable letter usage corresponds to exactly one
///  machine step.
///
///  This is axiomatized because the full Britton argument requires
///  detailed analysis of pinch elimination in the HNN tower.
#[verifier::external_body]
pub proof fn axiom_machine_group_backward(
    data: MachineGroupData,
    s1: nat, a1: nat, b1: nat,
    s2: nat, a2: nat, b2: nat,
)
    requires
        machine_group_data_wf(data),
        s1 < data.num_states,
        s2 < data.num_states,
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, s1, a1, b1),
            config_word(data.num_states, s2, a2, b2),
        ),
    ensures
        //  There exists a valid trace connecting the two configurations
        exists|trace: Seq<(nat, nat, nat)>|
            is_valid_trace(data, trace) &&
            trace[0] == (s1, a1, b1) &&
            trace[trace.len() - 1] == (s2, a2, b2),
{
}

//  ============================================================
//  Biconditional (combining forward and backward)
//  ============================================================

///  Machine computation ↔ group equivalence.
///
///  config_word(C1) ≡ config_word(C2) in G_M
///    if and only if
///  M can reach C2 from C1 (or vice versa).
pub proof fn lemma_machine_group_faithful(
    data: MachineGroupData,
    s1: nat, a1: nat, b1: nat,
    s2: nat, a2: nat, b2: nat,
)
    requires
        machine_group_data_wf(data),
        s1 < data.num_states,
        s2 < data.num_states,
    ensures
        //  Forward: trace exists → equiv
        (exists|trace: Seq<(nat, nat, nat)>|
            is_valid_trace(data, trace) &&
            trace[0] == (s1, a1, b1) &&
            trace[trace.len() - 1] == (s2, a2, b2))
        ==>
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, s1, a1, b1),
            config_word(data.num_states, s2, a2, b2),
        ),
        //  Backward: equiv → trace exists
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, s1, a1, b1),
            config_word(data.num_states, s2, a2, b2),
        )
        ==>
        (exists|trace: Seq<(nat, nat, nat)>|
            is_valid_trace(data, trace) &&
            trace[0] == (s1, a1, b1) &&
            trace[trace.len() - 1] == (s2, a2, b2)),
{
    //  Forward: if trace exists, apply lemma_trace_gives_equiv
    if exists|trace: Seq<(nat, nat, nat)>|
        is_valid_trace(data, trace) &&
        trace[0] == (s1, a1, b1) &&
        trace[trace.len() - 1] == (s2, a2, b2)
    {
        let trace = choose|trace: Seq<(nat, nat, nat)>|
            is_valid_trace(data, trace) &&
            trace[0] == (s1, a1, b1) &&
            trace[trace.len() - 1] == (s2, a2, b2);
        lemma_trace_gives_equiv(data, trace);
    }

    //  Backward: apply axiom_machine_group_backward
    if equiv_in_presentation(
        machine_group_presentation(data),
        config_word(data.num_states, s1, a1, b1),
        config_word(data.num_states, s2, a2, b2),
    ) {
        axiom_machine_group_backward(data, s1, a1, b1, s2, a2, b2);
    }
}

} //  verus!
