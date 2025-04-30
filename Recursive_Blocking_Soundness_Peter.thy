theory Recursive_Blocking_Soundness_Peter
  imports Graph_Theory_Peter
begin

(* ------------------------------------------------------------------------- *)
subsection ‹Basic predicates used only by the recursive-blocking theory›
(* ------------------------------------------------------------------------- *)

consts
  Coll        :: "node ⇒ path ⇒ bool"          ― ‹v is collider on p›
  NonC        :: "node ⇒ path ⇒ bool"          ― ‹v is non-collider on p›
  Endpoint    :: "node ⇒ path ⇒ bool"
  OnPath      :: "node ⇒ path ⇒ bool"
  AfterOnPath :: "node ⇒ node ⇒ path ⇒ bool"
  Halts       :: "node set ⇒ bool"
  (*ValidBlock  :: "node set ⇒ bool"*)
  Growsto     :: "node set ⇒ node set ⇒ bool"
  StrictSubset:: "node set ⇒ node set ⇒ bool"
  Initial     :: "node set"
  Adj         :: "node ⇒ node ⇒ bool"

(* Dummy constants used in some axioms ------------------------------------- *)
consts
  V  :: "node set"
  b1 :: "node set"

(* ------------------------------------------------------------------------- *)
subsection ‹Path-blocking definitions (unchanged)›
(* ------------------------------------------------------------------------- *)

definition HasNC :: "path ⇒ node set ⇒ bool" where
  "HasNC p f ≡ ∃x. NonC x p ∧ x ∉ f"

definition NoAfterInB :: "node ⇒ node set ⇒ path ⇒ bool" where
  "NoAfterInB v b p ≡ ∀d. AfterOnPath d v p ⟶ d ∉ b"

definition DirectedPath :: "node ⇒ node ⇒ node list ⇒ bool" where
  "DirectedPath x y p ≡
      p ≠ [] ∧ hd p = x ∧ last p = y ∧
      (∀i < length p - 1. Adj (p ! i) (p ! (i + 1)))"

definition Desc :: "node ⇒ node ⇒ bool" where
  "Desc x y ≡ (∃p. DirectedPath x y p)"

definition NoDescInB :: "node ⇒ node set ⇒ bool" where
  "NoDescInB c B ≡ ¬ (∃d. Desc c d ∧ d ∈ B)"

definition Blocked where
  "Blocked p B ≡ (∃v. NonC v p ∧ v ∈ B) ∨ (∀c. Coll c p ⟶ NoDescInB c B)"

definition Unblocked :: "path ⇒ node set ⇒ bool" where
  "Unblocked p b ≡ ¬ Blocked p b"

definition MSep :: "node ⇒ node ⇒ node set ⇒ bool" where
  "MSep x y B ≡ ¬ Adj x y ∧ (∀p. Blocked p B)"

definition Path :: "node ⇒ node ⇒ path ⇒ bool" where
  "Path x y p ⟷ hd p = x ∧ last p = y ∧ walk p"

definition walk_p :: "node list ⇒ bool" where
  "walk_p p ≡ walk p"

definition ValidBlock :: "node set ⇒ bool" where
  "ValidBlock B ≡ (∀p c. Coll c p ⟶ NoDescInB c B)"

(* ------------------------------------------------------------------------- *)
subsection ‹Three-way disjunction eliminator (helper lemma)›
(* ------------------------------------------------------------------------- *)

lemma disjE3:
  assumes "A ∨ B ∨ C"
    and AB: "A ⟹ R" and BB: "B ⟹ R" and CB: "C ⟹ R"
  shows R
  using assms by blast

lemma algorithm_preserves_invariant:
  "Algorithm_steps graph x y C F B ⟹ ValidBlock B"
  sorry

(* ------------------------------------------------------------------------- *)
subsection ‹High-level soundness via Lemma 3.1.1›
(* ------------------------------------------------------------------------- *)

lemma unblocked_path_contradicts_halting:
  assumes halts : "Halts B"
      and algo  : "Algorithm_steps graph x y C F B"
      and path  : "Path x y p"
      and unblk : "¬ Blocked p B"
  shows False
proof -
  have valid: "ValidBlock B"
  using algo
  by (rule algorithm_preserves_invariant)

  (* 1.  From ¬Blocked derive two concrete facts *)
  have no_nc_in_B: "¬(∃v. NonC v p ∧ v ∈ B)"
    using unblk unfolding Blocked_def by blast
  obtain c where coll_c: "Coll c p" and bad: "¬ NoDescInB c B"
    using unblk unfolding Blocked_def by (auto simp: not_all)

  (* 2.  Show that bad contradicts the global invariant *)
  from coll_c valid have "NoDescInB c B"
    unfolding ValidBlock_def by blast
  with bad show False by contradiction
qed

(* ------------------------------------------------------------------------- *)
subsection ‹Other theorems from your earlier draft (still with sorry)›
(* ------------------------------------------------------------------------- *)

lemma termination_lemma:
  fixes   V  :: "'a set"
    and   B  :: "'a set"
    and   Halts :: "'a set ⇒ bool"
  assumes "finite V" "B ⊆ V"
    and   "⋀B. B ⊆ V ⟹ ¬ Halts B ⟹ (∃B'. B ⊂ B' ∧ B' ⊆ V)"
  shows   "∃B. Halts B"
  sorry

(* … completeness, corollaries, etc. remain unchanged with their sorries … *)

end