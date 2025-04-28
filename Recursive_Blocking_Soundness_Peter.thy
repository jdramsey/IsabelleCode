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
  ValidBlock  :: "node set ⇒ bool"
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

definition Blocked :: "path ⇒ node set ⇒ bool" where
  "Blocked p b ≡
       (∃x. NonC x p ∧ x ∈ b) ∨
       (∀x. Coll x p ⟶ x ∉ b ∧ NoAfterInB x b p)"

definition Unblocked :: "path ⇒ node set ⇒ bool" where
  "Unblocked p b ≡ ¬ Blocked p b"

definition MSep :: "node ⇒ node ⇒ node set ⇒ bool" where
  "MSep x y B ≡ ¬ Adj x y ∧ (∀p. Blocked p B)"

definition Path :: "node ⇒ node ⇒ path ⇒ bool" where
  "Path x y p ⟷ hd p = x ∧ last p = y ∧ walk p"

definition walk_p :: "node list ⇒ bool" where
  "walk_p p ≡ walk p"

(* ------------------------------------------------------------------------- *)
subsection ‹Three-way disjunction eliminator (helper lemma)›
(* ------------------------------------------------------------------------- *)

lemma disjE3:
  assumes "A ∨ B ∨ C"
    and AB: "A ⟹ R" and BB: "B ⟹ R" and CB: "C ⟹ R"
  shows R
  using assms by blast

(* ------------------------------------------------------------------------- *)
subsection ‹High-level soundness via Lemma 3.1.1›
(* ------------------------------------------------------------------------- *)

theorem recursive_blocking_sound:
  assumes halts: "Halts B"
      and algo : "Algorithm_steps graph x y C F B"
  shows "∀p. Path x y p ⟶ Blocked p B"
proof (rule ccontr)
  assume not_all: "¬ (∀p. Path x y p ⟶ Blocked p B)"
  then obtain p where path: "Path x y p" and unblk: "Unblocked p B"
    by (auto simp: Blocked_def Unblocked_def)

  have walk_p: "walk p"
    sorry

  ― ‹1. every eligible non-collider must already be in B›
  have elig: "⋀v. NonC v p ⟶ v ∈ B"
    using halts algo path unblk
    sorry

  ― ‹2. From that and collider-closure derive a hop-wise d-connection›
  have hops:                   
    "⋀i. i + 1 < length p ⟹
         d_conn (p ! i) (p ! (i + 1)) B" 
    sorry

  ― ‹3. Chain the hops with Lemma 3.1.1›
  have d_conn_xy: "d_conn x y B"
    using lemma_3_1_1[of p, OF walk_p _ hops] .
                                         
  ― ‹4. Final sweep in the algorithm observed x ⟂ y | B ⇒ contradiction›
  moreover have "¬ d_conn x y B"
    using halts algo
    sorry
  ultimately show False by contradiction
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