use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;
use crate::homomorphism::*;

verus! {

///  Runtime symbol using usize indices (mirrors Symbol which uses nat).
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum RuntimeSymbol {
    Gen(usize),
    Inv(usize),
}

///  View: RuntimeSymbol → Symbol.
pub open spec fn runtime_symbol_view(s: RuntimeSymbol) -> Symbol {
    match s {
        RuntimeSymbol::Gen(i) => Symbol::Gen(i as nat),
        RuntimeSymbol::Inv(i) => Symbol::Inv(i as nat),
    }
}

///  View: Vec<RuntimeSymbol> → Word (Seq<Symbol>).
pub open spec fn runtime_word_view(w: Seq<RuntimeSymbol>) -> Word {
    Seq::new(w.len(), |i: int| runtime_symbol_view(w[i]))
}

//  --- Exec functions ---

///  Check if two runtime symbols form an inverse pair.
pub fn is_inverse_pair_exec(s1: &RuntimeSymbol, s2: &RuntimeSymbol) -> (out: bool)
    ensures
        out == is_inverse_pair(runtime_symbol_view(*s1), runtime_symbol_view(*s2)),
{
    match (s1, s2) {
        (RuntimeSymbol::Gen(i), RuntimeSymbol::Inv(j)) => *i == *j,
        (RuntimeSymbol::Inv(i), RuntimeSymbol::Gen(j)) => *i == *j,
        _ => false,
    }
}

///  Find the first cancellation position, or return w.len() if none.
pub fn find_cancellation_exec(w: &Vec<RuntimeSymbol>) -> (out: usize)
    requires
        w@.len() < usize::MAX,
    ensures
        out == find_cancellation_from(runtime_word_view(w@), 0),
{
    if w.len() <= 1 {
        return w.len();
    }
    let mut i: usize = 0;
    while i < w.len() - 1
        invariant
            0 <= i <= w.len() - 1,
            w@.len() < usize::MAX,
            find_cancellation_from(runtime_word_view(w@), 0)
                == find_cancellation_from(runtime_word_view(w@), i as nat),
        decreases w.len() - i,
    {
        if is_inverse_pair_exec(&w[i], &w[i + 1]) {
            return i;
        }
        i = i + 1;
    }
    w.len()
}

///  Reduce at position pos: remove elements at pos and pos+1.
pub fn reduce_at_exec(w: &Vec<RuntimeSymbol>, pos: usize) -> (out: Vec<RuntimeSymbol>)
    requires
        has_cancellation_at(runtime_word_view(w@), pos as int),
    ensures
        runtime_word_view(out@) == reduce_at(runtime_word_view(w@), pos as int),
{
    let mut result = Vec::with_capacity(w.len() - 2);
    let mut i: usize = 0;
    while i < pos
        invariant
            0 <= i <= pos,
            pos + 2 <= w.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == w@[k],
        decreases pos - i,
    {
        result.push(w[i]);
        i = i + 1;
    }
    //  Skip pos and pos+1
    let mut j: usize = pos + 2;
    while j < w.len()
        invariant
            pos + 2 <= j <= w.len(),
            result@.len() == (pos + (j - (pos + 2))) as int,
            forall|k: int| 0 <= k < pos ==> result@[k] == w@[k],
            forall|k: int| pos as int <= k < result@.len() ==>
                result@[k] == w@[k + 2],
        decreases w.len() - j,
    {
        result.push(w[j]);
        j = j + 1;
    }

    proof {
        let wv = runtime_word_view(w@);
        let rv = runtime_word_view(result@);
        let expected = reduce_at(wv, pos as int);
        //  expected = wv.subrange(0, pos) + wv.subrange(pos + 2, wv.len())
        assert(rv.len() == expected.len());
        assert(rv =~= expected);
    }
    result
}

///  Reduce a word to normal form.
pub fn reduce_word_exec(w: &Vec<RuntimeSymbol>) -> (out: Vec<RuntimeSymbol>)
    requires
        w@.len() < usize::MAX,
    ensures
        runtime_word_view(out@) == normal_form(runtime_word_view(w@)),
{
    let mut current = w.clone();
    let original_view: Ghost<Word> = Ghost(runtime_word_view(w@));

    //  fuel = w.len() / 2 is enough (each step removes 2 symbols)
    //  But we use w.len() for simplicity since reduce_n_steps uses w.len()
    let mut fuel: usize = w.len();

    proof {
        assert(runtime_word_view(current@) == runtime_word_view(w@));
        //  normal_form(wv) == reduce_n_steps(wv, wv.len())
        //  We'll maintain: normal_form(original) == reduce_n_steps(current_view, fuel)
    }

    while fuel > 0
        invariant
            current@.len() < usize::MAX,
            fuel <= w.len(),
            original_view@ == runtime_word_view(w@),
            normal_form(original_view@) == reduce_n_steps(runtime_word_view(current@), fuel as nat),
        decreases fuel,
    {
        let pos = find_cancellation_exec(&current);
        if pos >= current.len() {
            proof {
                let cv = runtime_word_view(current@);
                assert(find_cancellation_from(cv, 0) >= cv.len());
                //  No cancellation → word is reduced
                assert(!has_cancellation(cv)) by {
                    if has_cancellation(cv) {
                        let i = choose|i: int| has_cancellation_at(cv, i);
                        //  i >= 0 and i < cv.len() - 1
                        lemma_find_cancellation_from_none(cv, 0, i);
                        //  contradiction: not is_inverse_pair but has_cancellation_at
                    }
                }
                assert(is_reduced(cv));
                lemma_reduce_n_steps_reduced(cv, fuel as nat);
            }
            return current;
        }
        proof {
            let cv = runtime_word_view(current@);
            lemma_find_cancellation_from_valid(cv, 0);
            assert(has_cancellation_at(cv, pos as int));
        }
        let next = reduce_at_exec(&current, pos);
        proof {
            let cv = runtime_word_view(current@);
            let nv = runtime_word_view(next@);
            assert(nv == reduce_at(cv, pos as int));
            lemma_reduce_at_len(cv, pos as int);
        }
        current = next;
        fuel = fuel - 1;
    }
    proof {
        lemma_reduce_n_steps_zero(runtime_word_view(current@));
    }
    current
}

//  ============================================================
//  Runtime Homomorphism Application
//  ============================================================

///  Check that a runtime symbol's generator index is within the image array.
pub open spec fn runtime_symbol_valid_for_hom(s: RuntimeSymbol, num_images: int) -> bool {
    match s {
        RuntimeSymbol::Gen(i) => (i as int) < num_images,
        RuntimeSymbol::Inv(i) => (i as int) < num_images,
    }
}

///  Runtime homomorphism data: generator images as Vec of words.
pub struct RuntimeHomData {
    pub source_gen_count: usize,
    pub generator_images: Vec<Vec<RuntimeSymbol>>,
}

///  View RuntimeHomData as HomomorphismData (with placeholder presentations).
pub open spec fn runtime_hom_view(h: &RuntimeHomData) -> HomomorphismData {
    HomomorphismData {
        source: Presentation {
            num_generators: h.source_gen_count as nat,
            relators: Seq::empty(),
        },
        target: Presentation {
            num_generators: 0, //  placeholder — not used by apply_hom
            relators: Seq::empty(),
        },
        generator_images: Seq::new(h.generator_images@.len(), |i: int|
            runtime_word_view(h.generator_images@[i]@)),
    }
}

///  Inverse a runtime word: reverse and invert each symbol.
pub fn inverse_word_exec(w: &Vec<RuntimeSymbol>) -> (out: Vec<RuntimeSymbol>)
    ensures
        runtime_word_view(out@) =~= inverse_word(runtime_word_view(w@)),
    decreases w@.len(),
{
    let mut result = Vec::with_capacity(w.len());
    let mut i: usize = w.len();
    proof {
        if w@.len() == 0 {
            assert(runtime_word_view(result@) =~= empty_word());
            assert(inverse_word(runtime_word_view(w@)) =~= empty_word());
        }
    }
    while i > 0
        invariant
            0 <= i <= w.len(),
            result@.len() == (w.len() - i) as int,
            forall|k: int| 0 <= k < result@.len() ==>
                runtime_symbol_view(result@[k]) ==
                    inverse_symbol(runtime_word_view(w@)[(w@.len() - 1 - k) as int]),
        decreases i,
    {
        i = i - 1;
        let s = &w[i];
        let inv_s = match s {
            RuntimeSymbol::Gen(idx) => RuntimeSymbol::Inv(*idx),
            RuntimeSymbol::Inv(idx) => RuntimeSymbol::Gen(*idx),
        };
        result.push(inv_s);
    }

    proof {
        let wv = runtime_word_view(w@);
        let rv = runtime_word_view(result@);
        let expected = inverse_word(wv);
        crate::word::lemma_inverse_word_len(wv);
        assert(rv.len() == expected.len());
        //  Both have the same length and same elements
        assert(rv =~= expected) by {
            assert forall|k: int| 0 <= k < rv.len() implies rv[k] == expected[k] by {
                //  rv[k] = inv(wv[wv.len()-1-k])
                //  expected[k] = inverse_word(wv)[k]
                //  Need to show these are equal
                //  inverse_word reverses and inverts
                lemma_inverse_word_element(wv, k);
            }
        }
    }
    result
}

///  Helper: inverse_word element access.
pub proof fn lemma_inverse_word_element(w: Word, k: int)
    requires
        0 <= k < w.len(),
    ensures
        inverse_word(w)[k] == inverse_symbol(w[(w.len() - 1 - k) as int]),
    decreases w.len(),
{
    if w.len() == 0 {
        //  impossible
    } else {
        let rest = w.drop_first();
        crate::word::lemma_inverse_word_len(rest);
        //  inverse_word(w) = inverse_word(rest) + [inv(w.first())]
        //  inverse_word(w).len() == w.len()
        if k < inverse_word(rest).len() {
            //  k < rest.len(), so inverse_word(w)[k] == inverse_word(rest)[k]
            lemma_inverse_word_element(rest, k);
            //  inverse_word(rest)[k] == inv(rest[rest.len()-1-k])
            //  rest[rest.len()-1-k] == w[rest.len()-k] == w[w.len()-1-k]
            assert(rest[(rest.len() - 1 - k) as int] == w[(w.len() - 1 - k) as int]);
        } else {
            //  k == rest.len() == w.len()-1
            assert(k == (w.len() - 1) as int);
            assert(inverse_word(w)[k] == inverse_symbol(w.first()));
            assert(w[(w.len() - 1 - k) as int] == w[0]);
        }
    }
}

///  Apply homomorphism to a single symbol (exec).
pub fn apply_hom_symbol_exec(
    h: &RuntimeHomData,
    s: &RuntimeSymbol,
) -> (out: Vec<RuntimeSymbol>)
    requires
        match *s {
            RuntimeSymbol::Gen(i) => (i as int) < h.generator_images@.len(),
            RuntimeSymbol::Inv(i) => (i as int) < h.generator_images@.len(),
        },
    ensures
        runtime_word_view(out@) =~=
            apply_hom_symbol(runtime_hom_view(h), runtime_symbol_view(*s)),
{
    match s {
        RuntimeSymbol::Gen(i) => {
            h.generator_images[*i].clone()
        },
        RuntimeSymbol::Inv(i) => {
            inverse_word_exec(&h.generator_images[*i])
        },
    }
}

///  Append all elements from src to dst (exec helper).
fn append_vec(dst: &mut Vec<RuntimeSymbol>, src: &Vec<RuntimeSymbol>)
    ensures
        dst@ =~= old(dst)@ + src@,
{
    let ghost old_dst = dst@;
    let old_len = dst.len();
    let mut j: usize = 0;
    while j < src.len()
        invariant
            0 <= j <= src.len(),
            dst@.len() == old_len + j,
            dst@ =~= old_dst + src@.subrange(0, j as int),
        decreases src.len() - j,
    {
        dst.push(src[j]);
        proof {
            assert(src@.subrange(0, (j + 1) as int) =~=
                src@.subrange(0, j as int) + Seq::new(1, |_k: int| src@[j as int]));
            assert(Seq::new(1, |_k: int| src@[j as int]) =~= seq![src@[j as int]]);
        }
        j = j + 1;
    }
    proof {
        assert(src@.subrange(0, src@.len() as int) =~= src@);
    }
}

///  Helper: runtime_word_view of concatenated Vecs.
proof fn lemma_runtime_word_view_append(a: Seq<RuntimeSymbol>, b: Seq<RuntimeSymbol>)
    ensures
        runtime_word_view(a + b) =~= runtime_word_view(a) + runtime_word_view(b),
{
    let ab = a + b;
    let lhs = runtime_word_view(ab);
    let rhs = runtime_word_view(a) + runtime_word_view(b);
    assert(lhs.len() == rhs.len());
    assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
        if k < a.len() {
            assert(ab[k] == a[k]);
        } else {
            assert(ab[k] == b[(k - a.len() as int)]);
        }
    }
}

///  Helper: runtime_word_view of a subrange equals subrange of runtime_word_view.
pub proof fn lemma_runtime_word_view_subrange(w: Seq<RuntimeSymbol>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= w.len(),
    ensures
        runtime_word_view(w.subrange(lo, hi)) =~= runtime_word_view(w).subrange(lo, hi),
{
    let lhs = runtime_word_view(w.subrange(lo, hi));
    let rhs = runtime_word_view(w).subrange(lo, hi);
    assert(lhs.len() == rhs.len());
    assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
        assert(w.subrange(lo, hi)[k] == w[lo + k]);
    }
}

///  Apply homomorphism to a word (exec).
pub fn apply_hom_exec(
    h: &RuntimeHomData,
    w: &Vec<RuntimeSymbol>,
) -> (out: Vec<RuntimeSymbol>)
    requires
        forall|k: int| 0 <= k < w@.len() ==>
            runtime_symbol_valid_for_hom(#[trigger] w@[k], h.generator_images@.len() as int),
    ensures
        runtime_word_view(out@) =~=
            apply_hom(runtime_hom_view(h), runtime_word_view(w@)),
{
    let hv: Ghost<HomomorphismData> = Ghost(runtime_hom_view(h));
    let wv: Ghost<Word> = Ghost(runtime_word_view(w@));
    let mut result: Vec<RuntimeSymbol> = Vec::new();
    let mut i: usize = 0;

    while i < w.len()
        invariant
            0 <= i <= w.len(),
            forall|k: int| 0 <= k < w@.len() ==>
                runtime_symbol_valid_for_hom(#[trigger] w@[k], h.generator_images@.len() as int),
            hv@ == runtime_hom_view(h),
            wv@ == runtime_word_view(w@),
            runtime_word_view(result@) =~=
                apply_hom(hv@, wv@.subrange(0, i as int)),
        decreases w.len() - i,
    {
        let sym_image = apply_hom_symbol_exec(h, &w[i]);
        let ghost old_result_view: Word = runtime_word_view(result@);

        append_vec(&mut result, &sym_image);

        proof {
            let sub_i = wv@.subrange(0, i as int);
            let sub_i1 = wv@.subrange(0, (i + 1) as int);
            let singleton = Seq::new(1, |_j: int| wv@[i as int]);
            assert(sub_i1 =~= sub_i + singleton);

            //  apply_hom(sub_i + singleton) =~= apply_hom(sub_i) + apply_hom(singleton)
            crate::homomorphism::lemma_hom_respects_concat(hv@, sub_i, singleton);
            //  apply_hom(singleton) =~= apply_hom_symbol(wv@[i])
            crate::homomorphism::lemma_hom_singleton(hv@, wv@[i as int]);
            //  So: apply_hom(sub_i1) =~= apply_hom(sub_i) + apply_hom_symbol(wv@[i])

            //  wv@[i] == runtime_symbol_view(w@[i])
            assert(wv@[i as int] == runtime_symbol_view(w@[i as int]));

            //  result@ =~= old_bytes ++ sym_image@, and runtime_word_view distributes
            let ghost old_bytes = result@.subrange(0, (result@.len() - sym_image@.len()) as int);
            lemma_runtime_word_view_append(old_bytes, sym_image@);
            assert(result@ =~= old_bytes + sym_image@);
            assert(runtime_word_view(old_bytes) =~= old_result_view);
        }

        i = i + 1;
    }

    proof {
        assert(wv@.subrange(0, w@.len() as int) =~= wv@);
        lemma_runtime_word_view_subrange(w@, 0, w@.len() as int);
    }
    result
}

} //  verus!
