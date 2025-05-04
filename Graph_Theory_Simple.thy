theory Graph_Theory_Simple
  imports Main
begin

text \<open>Generic graph-theoretic definitions and d-separation lemmas used
      throughout the project.\<close>

(* ---------------------------------------------------------------- *)
section \<open>Primitive notions\<close>
(* ---------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
subsection \<open>Basic predicates used only by the recursive-blocking theory\<close>
(* ------------------------------------------------------------------------- *)

type_synonym node = nat  \<comment> \<open>or use any other type you prefer\<close>
type_synonym edge = "node \<times> node"
type_synonym path = "node list"  \<comment> \<open>treat a path as a list of vertices\<close>

consts
  Coll        :: "node \<Rightarrow> path \<Rightarrow> bool"          \<comment> \<open>v is collider on p\<close>
  NonC        :: "node \<Rightarrow> path \<Rightarrow> bool"          \<comment> \<open>v is non-collider on p\<close>
  Endpoint    :: "node \<Rightarrow> path \<Rightarrow> bool"
  OnPath      :: "node \<Rightarrow> path \<Rightarrow> bool"
  AfterOnPath :: "node \<Rightarrow> node \<Rightarrow> path \<Rightarrow> bool"
  Growsto     :: "node set \<Rightarrow> node set \<Rightarrow> bool"
  StrictSubset:: "node set \<Rightarrow> node set \<Rightarrow> bool"
  Initial     :: "node set"
  collider    :: "node \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool"   \<comment> \<open>middle vertex is a collider\<close>
  noncoll     :: "node \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool"   \<comment> \<open>middle vertex is a non-collider\<close>

record graph =
  V :: "node set"
  E :: "edge set"

(* Adjacency between two nodes in the graph *)
definition Adj :: "node \<Rightarrow> node \<Rightarrow> graph \<Rightarrow> bool" where
  "Adj x y G \<equiv> (x, y) \<in> E G"

text \<open>A *walk* is a (non-empty) list of vertices in which every pair of
      consecutive vertices is adjacent.\<close>
fun walk :: "path \<Rightarrow> graph \<Rightarrow> bool" where
  "walk [] _         \<longleftrightarrow> False" |
  "walk [_] _        \<longleftrightarrow> True"  |
  "walk (x # y # ws) G \<longleftrightarrow> Adj x y G \<and> walk (y # ws) G"

(* Activation of a path under conditioning set S *)
definition active :: "path \<Rightarrow> node set \<Rightarrow> graph \<Rightarrow> bool" where
  "active vs S G \<longleftrightarrow>
     walk vs G \<and> 
     (let n = length vs in
        (\<forall>i. 0 < i \<and> i + 1 < n \<longrightarrow>
             ((noncoll (vs ! (i - 1)) (vs ! i) (vs ! (i + 1)) \<longrightarrow> vs ! i \<notin> S) \<and>
              (collider (vs ! (i - 1)) (vs ! i) (vs ! (i + 1)) \<longrightarrow> vs ! i \<in> S))))"

(* d-connection via some active path *)
definition d_conn :: "node \<Rightarrow> node \<Rightarrow> node set \<Rightarrow> graph \<Rightarrow> bool" where
  "d_conn x y S G \<longleftrightarrow> (\<exists>P. hd P = x \<and> last P = y \<and> active P S G)"

(* Directed path from x to y *)
definition DirectedPath :: "node \<Rightarrow> node \<Rightarrow> path \<Rightarrow> graph \<Rightarrow> bool" where
  "DirectedPath x y p G \<equiv>
     p \<noteq> [] \<and> hd p = x \<and> last p = y \<and>
     (\<forall>i < length p - 1. Adj (p ! i) (p ! (i + 1)) G)"

(* y is a descendant of x *)
definition Desc :: "node \<Rightarrow> node \<Rightarrow> graph \<Rightarrow> bool" where
  "Desc x y G \<equiv> \<exists>p. DirectedPath x y p G"

(* No descendant of c is in the blocking set B *)
definition NoDescInB :: "node \<Rightarrow> node set \<Rightarrow> graph \<Rightarrow> bool" where
  "NoDescInB c B G \<equiv> \<not> (\<exists>d. Desc c d G \<and> d \<in> B)"

(* ABlocked: path is either blocked by a noncollider in B or all colliders lack descendants in B *)
definition ABlocked :: "path \<Rightarrow> node set \<Rightarrow> graph \<Rightarrow> bool" where
  "ABlocked p B G \<equiv> (\<exists>v. NonC v p \<and> v \<in> B) \<or> (\<forall>c. Coll c p \<longrightarrow> NoDescInB c B G)"

(* A path from x to y in the graph *)
definition Path :: "node \<Rightarrow> node \<Rightarrow> path \<Rightarrow> graph \<Rightarrow> bool" where
  "Path x y p G \<longleftrightarrow> hd p = x \<and> last p = y \<and> walk p G"

(* ---------------------------------------------------------------- *)
section \<open>Fundamental helper lemmas (placeholders for now)\<close>
(* ---------------------------------------------------------------- *)

lemma walk_concat_single:
  assumes "walk (xs @ [v]) G"
      and "walk (v # ys) G"
  shows   "walk (xs @ v # ys) G"
  sorry

lemma active_append:
  assumes seg1: "active (xs @ [a]) S1 G"
      and seg2: "active (a # ys)  S2 G"
      and mid:  "(noncoll (last xs) a (hd ys) \<longrightarrow> a \<notin> S2) \<and>
                 (collider (last xs) a (hd ys) \<longrightarrow> a \<in> S1)"
  shows  "active (xs @ a # ys) (S1 \<union> S2) G"
  sorry

lemma d_conn_bridge:
  assumes "d_conn x a T1 G"
      and "d_conn a y T2 G"
      and "(noncoll x a a \<and> a \<notin> T2) \<or> (collider x a a \<and> a \<in> T1)"
  shows  "d_conn x y (T1 \<union> T2) G"
  sorry

(* ---------------------------------------------------------------- *)
section \<open>Lemma 3.3.1 (Spirtes et al.)\<close>
(* ---------------------------------------------------------------- *)

definition hop :: "nat \<Rightarrow> node list \<Rightarrow> node set \<Rightarrow> graph \<Rightarrow> bool" where
  "hop i vs S G \<longleftrightarrow>
     d_conn (vs ! i) (vs ! (i + 1)) S G \<and>
     (noncoll (vs ! i) (vs ! (i + 1)) (vs ! (i + 1)) \<longrightarrow> vs ! (i + 1) \<notin> S) \<and>
     (collider (vs ! i) (vs ! (i + 1)) (vs ! (i + 2)) \<longrightarrow> vs ! (i + 1) \<in> S)"

definition hopS :: "nat \<Rightarrow> node list \<Rightarrow> graph \<Rightarrow> node set" where
  "hopS i vs G \<equiv> (SOME S. hop i vs S G)"

lemma lemma_3_1_1:
  fixes vs :: "node list"
  assumes walk: "walk vs G"
      and len:  "length vs \<ge> 2"
      and hops: "\<And>i. i < length vs - 1 \<Longrightarrow> hop i vs (hopS i vs G) G"
  shows "d_conn (hd vs) (last vs) (\<Union>i<length vs - 1. hopS i vs G) G"
  sorry

end