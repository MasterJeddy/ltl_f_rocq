# AI Usage Log — LTL / LTL_f equivalence (experimental agentic strand)

This document records interactions with Claude Code (AI assistant) for a **separate,
experimental strand** of the project: relating `ltl_expr` (in `ltl.v`) and `ltl_f_expr`
(in `ltl_f.v`). It is kept apart from `AI_USAGE_LOG.md` at the author's request.

Unlike the rest of the project — where the assistant was asked not to edit `.v` files so
that the Coq would be typed by the author — this strand was explicitly run as a "purely
agentic" experiment: the author asked the assistant to write the definitions and proofs
in `ltl.v` directly. **All Coq code in `ltl.v` from the `ltl_sat` definition onward was
written by the assistant, not the author.** The pre-existing `Section ltl` syntax and
`Stream`-based semantics are the author's, unchanged apart from two `Streams.`
qualifications noted in Entry 1.

---

## Entry 1

**Prompt:**
> The main goal of this repo was proving ltl-f equivalent to nbgw derived form it. This
> has been done, a second true fact is that ltl_f and ltl are logically equivlent ltl_f
> is a strict superset of ltl and from ltl_f when paired with any speccific real number r
> a equivalent ltl formula at most exponetially longer can be constructed. I want to
> expriment with a purely agentic approach for this equivalence ltl_f and ltl have been
> defined. Could you work purely in ltl.v and create two functions one that converts from
> ltl to ltl_f and one that goes for ltl_f + r to ltl (or a list of r called predicate)
> and then prove that the equivlence of both i.e. ltl_f pipe through it's function = r
> only when the converted formula is true. This is more exprimental and does not fall
> under the usual AI log for this project instead create a spereate
> AI_LTL_AND_LTL_F_LOG.md for this session.

Followed by two clarification exchanges. On the F_TERM blow-up the author asked:

> SO for the exponential blowup can possible values and the proof's around it not suffice
> for handlening this case.

and on the size bound:

> The size bound would be a nice to have but don't get stuck on it.

Author's design decisions, made via the clarification questions: interpret both logics
over `Computation AP` covering **both** finite and infinite traces; supply AND/OR/NOT as
abstract members of `F` constrained by hypotheses; treat the exponential size bound as
optional.

**Response summary:**

Added to `ltl.v` (the only `.v` file touched) a complete, fully-proved development
relating the two logics. No `Admitted`; `Print Assumptions` on every headline theorem
reports only the five classical/Reals axioms already used elsewhere in the project
(`proof_irrelevance`, `classic`, `constructive_indefinite_description`,
`functional_extensionality_dep`, `sig_forall_dec`).

*Shared semantics.* The existing `Stream AP` semantics cannot be compared with `ltl_f`
(there a state is a single AP symbol; in `ltl_f` it is a valuation `AP -> AtomicProposition`,
and computations may be finite). Added a second, boolean semantics for the *same* syntax
over `ltl_f`'s own model:

```coq
Fixpoint ltl_sat (c : Computation AP) (e : ltl_expr) : Prop
```

with `AP_TERM p` reading `value_of_ap_at_time AP c p 0 = Some AP1`, `NEXT` as
`nth_tail AP c 1`, and `UNTIL` as `exists i, … /\ forall j, (j < i)%nat -> …`. Finite
traces need no special case: past the end `value_of_ap_at_time` is `None`, matching
`sat_val = zero`.

*Key reused lemma.* Answering the author's question directly — yes, the existing
machinery suffices for `F_TERM`. `proof2`, `cartesian_product_correct`,
`possible_statsfaction_values` and `ltl_f_induction_principle` are exactly what the case
needs, and the proof mirrors `proof2.v`'s own `F_TERM` branch. The only genuinely new
supporting lemma is `cartesian_product_length`. Likewise the termination worry dissolved:
`sat_val` (`ltl_f.v:244`) already recurses under `ListDef.map` over the subformula list,
so mirroring that shape passes the guard checker with no `Program Fixpoint` or
`expr_size` recursion — confirmed by probe before any proof work.

*Bridge lemma* (`until_threshold`), the crux of both directions, obtained almost free
from `until_lemmas.v` (`until_achieved_bound` for ⇐; `sat_val_until_achieved` +
`until_is_achieved_iff` for ⇒):

```coq
v <= proj1_sig (sat_val c (ltl_f.UNTIL AP F e1 e2))
  <-> exists i, v <= proj1_sig (sat_val (nth_tail AP c i) e2)
             /\ forall j, (j < i)%nat -> v <= proj1_sig (sat_val (nth_tail AP c j) e1).
```

*Direction LTL_f + r → LTL* (`Section ltl_of_ltl_f`): `ge_ltl : ltl_f_expr AP F ->
UnitInterval -> ltl_expr AP`, structural, with `TRUE`/`FALSE`/`AP_TERM` guarded by
`Rle_dec (proj1_sig r) 0`, `NEXT`/`UNTIL` homomorphic, and `F_TERM f l` expanded into a
disjunction over `filter (fun args => ui_leb r (f_to_function f args)) (cartesian_product
(map psv l))`, each disjunct a conjunction pinning every argument's exact value. This is
where the exponential length lives. Also `eq_ltl e r := AND (ge_ltl e r) (NOT (big_or …
(above r (psv e))))`.

Theorems:

```coq
Theorem ge_ltl_correct : ltl_sat AP c (ge_ltl e r) <-> proj1_sig r <= proj1_sig (sat_val c e).
Theorem eq_ltl_correct : ltl_sat AP c (eq_ltl e r) <-> sat_val c e = r.
```

`ge_ltl_correct` by `ltl_f_induction_principle`; `eq_ltl_correct` falls out of the shared
`exactly_spec` lemma in three lines. Note `eq_ltl_correct` is the statement the author
asked for ("= r only when the converted formula is true"), and it is correct for *any*
`r`, including one outside `possible_statsfaction_values e` (then unsatisfiable).

*Direction LTL → LTL_f* (`Section ltl_f_of_ltl`): `ltl_to_ltl_f`, sending `AND`/`OR`/`NOT`
to `F_TERM` at abstract `f_and`/`f_or`/`f_not` constrained by

```coq
Hypothesis Hand : forall x y, f_to_function f_and [x; y] = unitinterval_min x y.
Hypothesis Hor  : forall x y, f_to_function f_or  [x; y] = unitinterval_max x y.
Hypothesis Hnot : forall x,   f_to_function f_not [x]    = unitinterval_comp x.
```

Proved `ltl_to_ltl_f_two_valued` (both halves simultaneously, avoiding a separate
"image is two-valued" induction), then

```coq
Theorem ltl_to_ltl_f_correct : ltl_sat AP c e <-> sat_val c (ltl_to_ltl_f e) = one.
```

*Capstone.* `ltl_round_trip : ltl_sat AP c e <-> ltl_sat AP c (ge_ltl (ltl_to_ltl_f e) one)`
— LTL is a retract of LTL_f, the precise sense in which the two are equally expressive
despite LTL_f being the larger syntax.

*Supporting definitions added:* `unitinterval_comp`, `zip_apply` (+ `zip_apply_length`,
`zip_apply_map_map`), `cartesian_product_length`, `ui_ltb`/`ui_leb` (+ specs), `above`
(+ `above_spec`), `big_or`/`big_and` (+ `big_or_correct`, `big_and_correct`),
`exactly_spec`, `forall2_sat_val_in_psv`, `zip_apply_pins_values`.

*Two incidental edits to the author's existing code*, both forced by importing `List`
alongside `Streams`, which shadows `hd`/`tl`: `is_ap` and `next` now read `Streams.hd` /
`Streams.tl`. Behaviour unchanged. Separately, `Section ltl`'s `true`/`false` stream
formulas shadow `bool`'s constructors; `ui_ltb`/`ui_leb` confine the resulting
`Datatypes.` qualification to one place.

*Not done:* the exponential size bound (`ltl_size (ge_ltl e r) <= 2 ^ (k * expr_size e)`),
deferred per the author's instruction not to get stuck on it. It would need
`length (cartesian_product ls) = product of lengths` and a bound on
`length (possible_statsfaction_values e)`, neither of which exists yet, and it is
independent of the equivalence proofs.

*Verification:* `rocq compile -Q . LTL_F_Project ltl.v` clean under Rocq 9.1.1; full
`make` over the regenerated Makefile clean (`ltl.v` was absent from `Makefile.conf`,
which predates the file); `Print Assumptions` checked on `ge_ltl_correct`,
`eq_ltl_correct`, `ltl_to_ltl_f_correct` and `ltl_round_trip`. Note that `Eval compute`
sanity checks are not meaningful here: `R` is axiomatic, so `Rle_dec` does not reduce.

---

## Entry 2

**Prompt:**
> So I got around to looking at the agnentic ltl implementation please check the two AI
> logs for details, firstly the paramater to the ltl[f] to ltl function is meant to be an
> exact match i.e. the ltl return true if the sat_val of the ltl[f] formula is equal to
> the paramter. Also is there a good reason ltl_sat is a fixpoint function and not an
> indutive Prop.

**Response summary:**

No `.v` file edited; answered in chat with one verified snippet.

*Exact match.* Pointed out that the exact-match function already exists and is the
headline result: `eq_ltl` (`ltl.v:232`) with
`eq_ltl_correct : ltl_sat AP c (eq_ltl e r) <-> sat_val c e = r` (`ltl.v:396`), correct
for any `r` (unsatisfiable when `r` is outside `psv e`). Explained why `ge_ltl` exists as
the internal workhorse rather than compiling equality directly: `until_threshold` is
inherently a `<=` statement, because `sat_val (UNTIL e1 e2)` is a max over `i` of a min,
so `v <= sat_val (UNTIL ...)` distributes structurally into the `exists i / forall j < i`
shape whereas an equality does not (the max may be attained at any `i`, leaving the other
positions unconstrained). Exactness is then recovered by `>= r` conjoined with the denial
of `>= w` for every larger `w` in `above r (psv e)`, finite by
`possible_statsfaction_values` — that is `exactly_spec` (`ltl.v:241`), also used to pin
arguments in the `F_TERM` case.

Flagged one inconsistency: the capstone `ltl_round_trip` (`ltl.v:555`) is still stated
with `ge_ltl ... one` rather than the exact-match function (equivalent at threshold `one`
since `sat_val <= 1`, but off-message). Gave a replacement, compiled successfully against
a scratch copy of the whole project:

```coq
Theorem ltl_round_trip_exact : forall (e : ltl_expr AP) (c : Computation AP),
  ltl_sat AP c e <-> ltl_sat AP c (eq_ltl AP F f_to_function (ltl_to_ltl_f e) one).
Proof.
  intros e c. rewrite (eq_ltl_correct AP F f_to_function).
  apply ltl_to_ltl_f_correct.
Qed.
```

*Fixpoint vs Inductive.* Yes, there is a hard reason: `NOT` forces a clause
`sat_not : ~ sat c e -> sat c (NOT e)`, a non-strictly-positive occurrence. Verified by
actually submitting such an `Inductive` to Rocq, which reports
`Non strictly positive occurrence of "sat" in "forall (c : C) (e : ltl_expr), ~ sat c e
-> sat c (NOT e)"`. The workarounds (mutual `sat`/`unsat` with a completeness proof, a
polarity index, or restricting to negation normal form) buy nothing here, since recursion
is structural on `e` and `ltl_expr`'s own induction principle already supplies what
`induction`/`inversion` on a relation would, while `simpl`/`cbn` unfolds every connective
definitionally — which is why `big_or_correct` and `exactly_spec` need no per-constructor
inversion lemmas. Added that `UNTIL`'s `exists i, ... /\ forall j < i, ...` clause is the
closed form of the least fixed point an `Inductive` would give, that the (now deleted)
`Inductive until` in the Stream semantics was legal only because its `P`/`Q` are abstract
predicates rather than the relation being defined, and that `Prop` rather than `bool` is
forced because `UNTIL` quantifies over all of `nat` on possibly-infinite traces.

*Verification:* `rocq compile -Q . LTL_F_Project ltl.v` clean on the current working copy
(which has the author's deletion of the old `Stream`-based semantics section), and clean
again on a scratch copy with `ltl_round_trip_exact` appended.

---

## Entry 3

**Prompt:**
> Could you rework the conversion to instead of working with a single value r work with
> a list of Uniterval P and determine if sat_val is in P. An can this be done without
> signatifcantly increasing the ltl formula.

**Response summary:**

Edited `ltl.v` directly (this strand is the agentic one; see the header). Purely
additive — no existing definition, statement or proof was changed. Compiles clean under
Rocq 9.1.1 (`rocq compile -Q . LTL_F_Project ltl.v`), no `Admitted`, and
`Print Assumptions` on `in_ltl_correct`, `in_ltl_trim_correct`, `exact_ltl_correct` and
`trim_length` reports only the project's five existing axioms (`sig_forall_dec`,
`proof_irrelevance`, `functional_extensionality_dep`,
`constructive_indefinite_description`, `classic`) — `Req_EM_T` introduces nothing new.

*Generic helpers (before `Section ltl_connectives`).* `ui_eq_dec` (decidable equality on
`UnitInterval`, via `Req_EM_T` plus `unitinterval_eq`, declared `Defined` since it is used
to build formulas), `ui_ltb_false`, `min_of : list UnitInterval -> option UnitInterval`
(least element) with `min_of_none` and
`min_of_some : min_of l = Some w -> In w l /\ forall u, In u l -> proj1_sig w <= proj1_sig u`,
and `min_above v l := min_of (above v l)` — the successor of `v` in the finite set `l` —
with `min_above_none` and `min_above_some`.

*New material in `Section ltl_of_ltl_f`.*

```coq
Definition range_ltl (e) (a : UnitInterval) (w : option UnitInterval) : ltl_expr AP :=
  match w with None => ge_ltl e a | Some u => AND AP (ge_ltl e a) (NOT AP (ge_ltl e u)) end.
Definition exact_ltl (e) (v : UnitInterval) : ltl_expr AP := range_ltl e v (min_above v (psv e)).
Definition in_ltl (e) (P : list UnitInterval) : ltl_expr AP :=
  big_or AP (ListDef.map (fun v => exact_ltl e v) P).
Definition trim (e) (P) : list UnitInterval :=
  nodup ui_eq_dec (filter (fun v => if in_dec ui_eq_dec v (psv e)
                                    then Datatypes.true else Datatypes.false) P).
```

with `range_ltl_correct` (`a <= sat_val` and `sat_val < u` when the bound is `Some u`),
`exact_ltl_correct : ltl_sat AP c (exact_ltl e v) <-> sat_val c e = v` — unconditional in
`v`, including `v` outside `psv e`, where both the `None` and `Some` shapes come out
unsatisfiable — the headline

```coq
Theorem in_ltl_correct : ltl_sat AP c (in_ltl e P) <-> In (sat_val c e) P.
```

and `in_ltl_singleton`, `trim_spec`, `trim_length`, `in_ltl_trim_correct`. Also
`exact_ltl_eq_ltl : ltl_sat AP c (exact_ltl e r) <-> ltl_sat AP c (eq_ltl e r)`, recording
that the new single-value formula is semantically the old one.

*Size — the answer to the second question.* Yes, at no significant cost. The key is that
`sat_val c e` always lies in `psv e` (`proof2`), so "exactly `v`" need only exclude `v`'s
*successor* in `psv e` rather than every larger candidate as `eq_ltl` does: `exact_ltl`
uses two copies of `ge_ltl` where `eq_ltl` uses `1 + length (above r (psv e))`. Hence
`in_ltl e P` costs `2 * length P` copies, and `in_ltl e (trim e P)` at most
`2 * length (psv e)` — i.e. within a factor of two of what a *single* value cost before,
for any `P` whatever, which is the content of `trim_length`. The exponential in `ge_ltl`'s
`F_TERM` case is untouched and unduplicated per extra value. Noted the remaining
optimisation, not implemented: adjacent values merge, so a `P` that is a union of `k`
runs of consecutive `psv e` values needs only `2 * k` copies via `range_ltl` directly
(one `ge_ltl` for an upward-closed `P`), independent of `length P`; doing this in general
needs `psv e` sorted, which the development does not currently have.

Also observed that the author's `ltl_round_trip_exact` (added between sessions) may now
use `exact_ltl ... one` in place of `eq_ltl ... one` for a smaller formula, the two being
interchangeable by `exact_ltl_eq_ltl`; left unchanged.

---

## Entry 4

**Prompt:**
> Could you also please do a bound proof on the maxium length of the resultant ltl
> expression

**Response summary:**

Edited `ltl.v` directly (agentic strand), purely additively. Compiles clean under Rocq
9.1.1; the whole project also builds from a regenerated Makefile (`./build.sh`, which
globs `*.v`) with no errors. No `Admitted`. `Print Assumptions` on both closed-form
theorems reports only axioms already used in the project. This completes the size bound
deferred in Entry 1.

*Measure.* `Fixpoint ltl_size (e : ltl_expr) : nat` in `Section ltl`, counting nodes.

*List helpers* (before `Section ltl_connectives`): `length_filter_le`, `in_list_sum_le`,
`zip_apply_length_le`, `zip_apply_in` (`In y (zip_apply fs xs) -> exists g, In g fs /\
exists x, In x xs /\ y = g x`). In `Section ltl_connectives`: `big_or_size` and
`big_and_size`, both of the form
`(forall x, In x l -> ltl_size x <= m) -> ltl_size (big_or l) <= 1 + length l * (1 + m)`.

*Structural bound* (end of `Section ltl_of_ltl_f`). `Fixpoint ge_bound : ltl_f_expr AP F
-> nat` mirrors `ge_ltl` with `r` erased -- `r` only chooses `TRUE`/`FALSE` at the leaves
and prunes the `filter`, which can only shrink the formula -- its `F_TERM` case being

```coq
1 + length (cartesian_product (map psv l))
    * (2 + length l * (1 + list_sum (map (fun e0 => 3 + ge_bound e0
                                    + length (psv e0) * (1 + ge_bound e0)) l)))
```

with `tbl_entry_size` (one table entry costs `3 + ge_bound e0 + length (psv e0) *
(1 + ge_bound e0)`), `f_term_size_le` (the `F_TERM` case isolated from the induction), and

```coq
Theorem ge_ltl_size_le : ltl_size AP (ge_ltl e r) <= ge_bound e.          (* uniform in r *)
Lemma   exact_ltl_size_le : ltl_size AP (exact_ltl e v) <= 2 + 2 * ge_bound e.
Theorem in_ltl_size_le : ltl_size AP (in_ltl e P) <= 1 + length P * (3 + 2 * ge_bound e).
Theorem in_ltl_trim_size_le :
  ltl_size AP (in_ltl e (trim e P)) <= 1 + length (psv e) * (3 + 2 * ge_bound e).
```

The last one is the answer to Entry 3's size question in proved form: after trimming, the
bound does not mention `P` at all.

*Closed form* (new `Section closed_size_bound` at the end of the file, after a
`From LTL_F_Project Require Import bounds.` placed there deliberately -- importing
`bounds` (and through it `nbgw_for_ltl_f`, `ngbw`) at the top of the file would put more
homonymous constructors in scope for the earlier sections). Arithmetic helpers
`pow2_ge_1`, `pow2_mono`, `pow2_le_mono`, `pow2_add_le`, `pow2_mul_le`, `n_le_pow2`,
`list_sum_le_length_mul`; project helpers `expr_size_ge_1`, `ge_bound_ge_1`,
`length_le_sum_sizes`, `in_le_sum_sizes`. Then, reusing the author's own
`possible_statsfaction_values_bounded` (`length (psv e) <= 2 ^ expr_size e`) and
`length_possible_values_from_possible_args` from `bounds.v`:

```coq
Theorem ge_bound_exponential : ge_bound e <= 2 ^ (5 * expr_size e * expr_size e).
Theorem ge_ltl_size_exponential :
  ltl_size AP (ge_ltl e r) <= 2 ^ (5 * expr_size e * expr_size e).
Theorem in_ltl_size_exponential :
  ltl_size AP (in_ltl e (trim e P)) <= 2 ^ (5 * expr_size e * expr_size e + expr_size e + 3).
```

The `F_TERM` case (`f_term_bound_exponential`) is where all the factors meet: with
`S = sum_list_elements_nat (map expr_size l)` and `n = 1 + S`, the number of tuples is
`length (psv (F_TERM f l)) <= 2 ^ n`, each conjunct is at most `2 ^ (5*S*S + S + 3)`, and
chaining the multiplications gives exponent `3n + (5*S*S + S + 3) + 3 = 5*S*S + 4*S + 9`,
which is at most `5*n*n = 5*S*S + 10*S + 5` exactly when `S >= 1` -- i.e. for every
`F_TERM` with at least one argument, the empty-argument case being discharged by
computation (`ge_bound = 3 <= 2 ^ 5`). Noted that the constant 5 is not optimal, merely
the smallest that makes the induction close (it needs `k * (2n - 1) >= 4n + 5`), and that
the exponent is quadratic in the formula size, not linear.

---

## Entry 5

**Prompt:**
> Here I need an honset answer does the quadratic in formula size still me the same as
> expotential in I am here asking a terminology question, I am a computer scientist not a
> matmatcian and want to check that we proved the right thing.

**Response summary:**

No Coq written; terminology and scope-of-claim answer about Entry 4's bound.

Stated plainly that `2 ^ (5 * n * n)` is *not* "exponential" in the strict sense used in
the temporal-logic literature: a function is singly (simply) exponential when it is
`2 ^ O(n)`, i.e. bounded by `c ^ n` for a constant `c`, and `2 ^ (n * n)` exceeds every
`c ^ n` (take `n > log2 c`). It is exponential in the looser complexity-class sense
(`2 ^ poly(n)`, i.e. in EXP), and it is definitely not doubly exponential. Warned that in
this subfield "exponential blow-up" conventionally means `2 ^ O(|phi|)` -- the classical
LTL-to-Buechi bound, and the same shape as the project's own
`possible_statsfaction_values_bounded` -- so an unqualified "at most exponentially
longer" in the report would be read as a stronger claim than Entry 4 proves.

Argued (informally, not formalised) that the quadratic exponent is inherent to the
translation rather than slack in the proof, via the family `e0 = AP_TERM p`,
`ej = F_TERM fj [AP_TERM q, e(j-1)]` with each `fj` injective: then
`length (psv ej) = 2 ^ (j+1)`, `expr_size ej = 2j+1`, and for `r` near 0 the `filter`
prunes nothing, so each nesting level multiplies the tree by about `2 ^ (2j)`, giving
roughly `2 ^ (n * n / 4)` against the proved `2 ^ (5 * n * n)`. The constant 5 is loose;
the quadratic is not.

Recommended either (1) reporting the proved statement as "`2 ^ O(n^2)`, singly
exponential with a quadratic exponent" rather than bare "exponential", or (2) changing
the measure: counted as a DAG with sharing, the distinct subformulas are at most
`n * 2 ^ n` "argument `e0` takes value `v`" gadgets plus at most `n * 2 ^ n` conjunction
spines per `F_TERM`, so the DAG size is `2 ^ O(n)` and the quadratic is an artifact of
unfolding to a tree. Noted that option (2) needs `ltl_size` replaced by a
distinct-subformula count (new Coq; the correctness proofs are unaffected), and that the
bound already in `ltl.v` is a correct upper bound either way -- the question is only
which sentence it licenses.

---

## Entry 6

**Prompt:**
> As an expriment could you try 1 or two different approaches the generating and LTL
> forumal to see if it could fit the exponetial bound in a scratch pad. If you can't that
> is fine and I'll simply report what you found but please try to dig deeper, and please
> don't change the existing LTL[F] defintion.

**Response summary:**

Experiment run entirely in the session scratchpad. `ltl_f.v` untouched, as instructed; no
project file was edited this turn.

*Measurement harness.* A python model (`scratchpad/exp/model.py`) of the exact tree-size
recursions, validated against the real Coq development: it reproduces `ge_bound` exactly
(145 at d=1, 11873 at d=2 on the Boolean caterpillar, matching `Eval vm_compute`; Coq
cannot go further only because `nat` is unary). Families used: Boolean caterpillar
`e_j = F_TERM f [AP, e_{j-1}]`, NEXT caterpillar, UNTIL caterpillar
`e_j = F_TERM f [AP, UNTIL(AP, e_{j-1})]`, and the balanced Boolean tree.

*Approach 1 -- table-based compilation (implemented AND proved, `scratchpad/p4/flat.v`,
207 lines, compiles clean, no `Admitted`, same five axioms).* Instead of recursing once
per threshold, the recursion carries a whole table: every value a subformula can take,
paired with an `ltl` formula holding exactly when it takes it. `F_TERM` and `NEXT` are
transparent, so a whole Boolean/`NEXT` block is compiled once instead of once per nesting
level:

```coq
Fixpoint table (e : ltl_f_expr AP F) : list (UnitInterval * ltl_expr AP) :=
  match e with
  | ltl_f.F_TERM _ _ f l =>
      map (fun row => (f_to_function f (map fst row), big_and AP (map snd row)))
        (cartesian_product (map table l))
  | ltl_f.NEXT _ _ e' => map (fun row => (fst row, NEXT AP (snd row))) (table e')
  | _ => map (fun v => (v, exact_ltl e v)) (psv e)
  end.
Definition ge_flat e r := big_or AP (map snd (filter (fun row => ui_leb r (fst row)) (table e))).
Definition in_flat e P := big_or AP (map snd (filter (in_dec ui_eq_dec (fst row) P) (table e))).
```

with `table_sound`, `table_complete` and the headline
`ge_flat_correct : ltl_sat AP c (ge_flat e r) <-> proj1_sig r <= proj1_sig (sat_val c e)`
and `in_flat_correct : ltl_sat AP c (in_flat e P) <-> In (sat_val c e) P`. Reuses
`exact_ltl_correct`, `proof2`, `big_and_correct`, `big_or_correct`,
`cartesian_product_correct`; needed one genuinely new lemma, `cartesian_product_sound`
(the converse of `cartesian_product_correct`), which the project did not have.

Measured log2 tree size, current construction vs `table`:

| family | n | current | table |
|---|---|---|---|
| Boolean caterpillar | 33 | 276 | 23 |
| NEXT caterpillar | 43 | 214 | 21 |
| balanced Boolean tree | 63 | 96 | 39 |
| UNTIL caterpillar | 45 | 168 | 157 |

So the quadratic exponent is removed outright for the `UNTIL`-free fragment -- fitted
`log2 size ~ n^1.97` becomes linear -- and survives when `UNTIL`s sit under `F_TERM`s.

*Approach 2 -- also tabulate `UNTIL`* (drop the fall-back to `ge_ltl`: build each
`UNTIL` row as `(ge from t1) U (ge from t2)` conjoined with the denial of the successor).
Modelled only, not implemented: on the UNTIL caterpillar log2 size falls from 168 to 109
at n=45, but the fitted exponent stays super-linear (~n^1.6, heading to quadratic). The
product `|psv(UNTIL)| x (size of the UNTIL's compiled formula)` is untouched by the
change.

*Conclusion.* A row of an `F_TERM` block must pin the exact value of every leaf; when a
leaf is an `UNTIL` there can be exponentially many values and its gadget is itself
exponentially large, and each row needs its own copy. A tree cannot share them. The two
escapes are the DAG/closure measure, or fresh atomic propositions naming subformula
values -- which leaves plain `ltl` over the original alphabet. Recommended, if the
construction is to be changed at all, that `table` replaces `ge_ltl` (strictly smaller,
already proved correct, gives `2 ^ O(n)` on the `UNTIL`-free fragment), while noting that
it does not license a `2 ^ O(n)` claim in general. Also noted that no `ltl_size` bound for
`ge_flat` was proved -- the size claims for it are measured, not formalised.

---

## Entry 7

**Prompt:**
> So the core problem here is UNTIL can you make clear to me why until needs to check each
> value in psv, the intutive on paper proof simply keeps the until keeps until forumlas the
> same convert (phi U phi2) becomes (conver phi1) U (conver phi2) why is this not done in
> your conversion. I can understand this shorter conversion makes until case hardee to
> proof but does in make it impossible.

**Response summary:**

No code written; correction and explanation.

Pointed out that the homomorphic clause the author describes *is* what is implemented --
`ltl.v:363`, `| ltl_f.UNTIL _ _ e1 e2 => UNTIL AP (ge_ltl e1 r) (ge_ltl e2 r)` -- with the
threshold carried through unchanged; its correctness branch is ten lines
(`rewrite until_threshold` plus the two IHs) and its size clause is additive
(`1 + ge_bound e1 + ge_bound e2`, `ltl.v:696`). `psv` occurs in exactly one clause of
`ge_ltl`, the `F_TERM` one. So `UNTIL` never enumerates values for its own sake, and
nothing there was avoided or found impossible. Corrected the previous entry's phrasing
("UNTIL is the wall"), which was imprecise.

Explained where the duplication really comes from: `f` is arbitrary, so `f(args) >= r`
does not decompose into threshold tests on the arguments; each branch must pin every
argument's exact value, and "argument `= v`" is a threshold pair at `v` and its successor.
For `e = F_TERM f [a, U]` with `U = b U c`, `ge(e,r)` is a disjunction over tuples `(x,v)`
of `(a = x) /\ (U = v)` with `(U = v) = (ge(b,v) U ge(c,v)) /\ ~(ge(b,v+) U ge(c,v+))`, so
the homomorphic `U` clause is instantiated `2 x (number of tuples)` times. The
duplication is imposed from above by `F_TERM`, not generated inside the `UNTIL` case.
Also explained why `table` (Entry 6) can flatten `NEXT` but not `UNTIL`: the value of
`NEXT e'` at time `t` is the value of `e'` at `t+1`, so one row maps to one row, whereas
the value of `e1 U e2` is a max-min over unboundedly many positions and is not a function
of the children's values at the current position.

Main point for the report: the exponential is the price of *arbitrary function symbols*,
not of temporal operators. For the usual fuzzy connectives each argument appears once --
`ge(min(x,y),r) = ge(x,r) /\ ge(y,r)`, `ge(max(x,y),r) = ge(x,r) \/ ge(y,r)`,
`ge(1-x,r) = ~ge(x,w+)` with `w = 1-r` -- so the translation is homomorphic and linear in
the formula size, with `psv` consulted only at compile time to choose a threshold (exactly
what `min_above` does), never to multiply the formula. The general condition is that the
up-set `{args : f args >= r}` be a union of few boxes in the product order; min/max/comp
need one, an arbitrary `f` needs exponentially many (Shannon counting).

Offered, not done: add `Hand`/`Hor`/`Hnot`-style hypotheses on the `F` side, define the
homomorphic `ge_hom`, and prove `ge_hom_correct` together with
`ltl_size (ge_hom e r) <= k * expr_size e` -- a linear bound with no `psv` and no
exponent, mirroring the hypotheses already used by `ltl_to_ltl_f`.

---

## Entry 8

**Prompt:**
> Okay what prevent something like the followin pseudo code from working convert fun (expr
> : ltl_f) (r : UnitInteval) match expr with | ltl_f.TRUE => if r = 1 then TRUE else FALSE
> | ltl_f.FALSE => if r = o then TRUE else FALSE | ltl_f.AP_TERM p => (if r = 1 then
> AP_TERM p else (if r = 0 then NOT (AP_TERM p) else FALSE) | ltl_f.F_TERM p => something
> similiar to big and big or construction to check possible arg where f = r or flase if not
> | ltl_f.NEXT e => convert e | ltl_f.UNTIL e1 e2 => (convert e1) U (convert e2) end.

**Response summary:**

No project code changed; analysis plus measurement (model extended in
`scratchpad/exp/model.py`).

Verdict: five of the six clauses are correct as written, and the `F_TERM` clause is
strictly better than what is in `ltl.v`. The `UNTIL` clause is the one that fails, and it
fails in both directions. Gave two counterexamples with `r = 1/2`:

- *Unsound*: `sat_val e2` is `1/2` at position 0 and `1` at position 1, `sat_val e1` is `1`
  at position 0. Then `(e1 = 1/2) U (e2 = 1/2)` holds with witness `i = 0`, but the real
  value is `1` (witness `i = 1`, since `e2@1 = 1` and `e1@0 = 1`).
- *Incomplete*: `sat_val e2` is `0, 1/2, 0, 0, ...` and `sat_val e1` is `1, 0, 0, ...`.
  The candidates `min(e2@i, min_{j<i} e1@j)` are `0, 1/2, 0, ...`, so the value is exactly
  `1/2`, yet `(e1 = 1/2) U (e2 = 1/2)` is false (the only position with `e2 = 1/2` is 1,
  and there `e1@0 = 1`).

Reason: `sat_val (e1 U e2) = max_i min(e2@i, min_{j<i} e1@j)`, and thresholds distribute
over both extrema -- `v <= max_i X_i <-> exists i, v <= X_i` and
`v <= min_j Y_j <-> forall j, v <= Y_j`, which is exactly `until_threshold` and is why the
homomorphic clause is valid *for `>=`*. Equality has no such law: `max_i X_i = v` is
`(exists i, X_i >= v) /\ (forall i, X_i <= v)`, a lower *and* an upper bound, i.e.
irreducibly two threshold statements. The achieving index only makes the *minimum* of a
set equal `r` (its members are merely `>= r`, counterexample B), and a later index may
beat it outright (counterexample A). Hence an exact conversion cannot be primitive: at
`UNTIL` it must be `ge(U,v) /\ ~ge(U,v+)`, which is why `ge_ltl` exists and `exact_ltl` is
layered on top of it rather than the reverse. Noted this is the same root cause as the
Entry 6 flattening failure -- `UNTIL`'s value is not a function of its children's values at
the current position but an extremum over the whole future; every pointwise clause
(`TRUE`, `FALSE`, `AP_TERM`, `F_TERM`, `NEXT`) admits both an exact clause and
table-flattening, and `UNTIL` admits neither.

On the `F_TERM` clause, which is a genuine improvement: the current code spends
`1 + length (psv e0)` copies of an argument's formula per branch entry (2 with the
`min_above` version of `exact_ltl`), whereas a native exact conversion spends one. The
saving compounds across nesting levels. Measured log2 tree size on the Boolean
caterpillar: current `76 / 136 / 214` at `n = 17 / 23 / 29`, the exact scheme
`47 / 80 / 122`, `table` from Entry 6 `14 / 18 / 21`. The exact scheme's fitted exponent is
`n^1.84` against the current `n^1.96` -- a constant-factor win in the exponent, still
quadratic, because it still emits one branch per tuple with the child inlined in each; only
the table construction removes the compounding. On the UNTIL caterpillar the two are
indistinguishable.

Minor notes: `| NEXT e => convert e` needs the wrapper `NEXT (convert e r)`, and the
`r = 1` / `r = 0` tests need `ui_eq_dec`. Offered to build the mutual pair (`exact_conv`
for the pointwise clauses, falling back to `ge_ltl` at `UNTIL`) in the scratchpad and
measure it.
