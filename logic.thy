theory logic
  imports Main
begin

record 'a language =
  rels :: "nat \<Rightarrow> 'a set" ("_\<^sup>R")
  funs :: "nat \<Rightarrow> 'a set" ("_\<^sup>F")

record ('a, 'b) struct =
  lang :: "'a language"
  underlying :: "'b set" ("_\<^sup>U")
  rel_interp :: "'a \<Rightarrow> 'b list set"
  fun_interp :: "'a \<Rightarrow> 'b list \<Rightarrow> 'b"

definition member_struct :: "'b \<Rightarrow> ('a, 'b) struct \<Rightarrow> bool" (infix ":\<in>" 50) where
  "x :\<in> \<A> \<equiv> x \<in> underlying \<A>"

definition tuples :: "('a, 'b) struct \<Rightarrow> nat \<Rightarrow> 'b list set" ("_\<^sup>_") where
  "\<A>\<^sup>n \<equiv> let A = underlying \<A> in { l . list.set l \<subseteq> A \<and> length l = n }"

definition is_struct :: "'a language \<Rightarrow> ('a, 'b) struct \<Rightarrow> bool" where
  "is_struct \<L> \<A> \<equiv> (lang \<A> = \<L>) \<and>
                    (\<forall>m. \<forall>r \<in> \<L>\<^sup>R m. \<forall>l. length l \<noteq> m \<longrightarrow> l \<notin> rel_interp \<A> r) \<and>
                    (\<forall>n. \<forall>f \<in> \<L>\<^sup>F n. \<forall>l \<in> \<A>\<^sup>n. fun_interp \<A> f l :\<in> \<A>)"

definition hom :: "('a, 'b) struct \<Rightarrow> ('a, 'c) struct \<Rightarrow> ('b \<Rightarrow> 'c) set" where
  "hom \<A> \<B> \<equiv>
     { h . 
     let \<L> = lang \<A> in \<L> = lang \<B> \<and> is_struct \<L> \<A> \<and> is_struct \<L> \<B> \<and>
      (\<forall>m. \<forall>r \<in> \<L>\<^sup>R m. \<forall>l \<in> \<A>\<^sup>m. l \<in> rel_interp \<A> r \<longrightarrow> (map h l) \<in> rel_interp \<B> r) \<and>
      (\<forall>n. \<forall>f \<in> \<L>\<^sup>F n. \<forall>l \<in> \<A>\<^sup>n. h (fun_interp \<A> f l) = fun_interp \<B> f (map h l)) }"
declare Let_def[simp]

lemma homI[intro]: "\<lbrakk> is_struct \<L> \<A> ; is_struct \<L> \<B> ; \<L> = lang \<A> ; lang \<A> = lang \<B>;
               \<forall>m. \<forall>r \<in> \<L>\<^sup>R m. \<forall>l \<in> \<A>\<^sup>m. l \<in> rel_interp \<A> r \<longrightarrow> (map h l) \<in> rel_interp \<B> r;
               \<forall>n. \<forall>f \<in> \<L>\<^sup>F n. \<forall>l \<in> \<A>\<^sup>n. h (fun_interp \<A> f l) = fun_interp \<B> f (map h l) \<rbrakk> 
              \<Longrightarrow> h \<in> hom \<A> \<B>"
  by (auto simp: hom_def)

definition strong_hom :: "('a, 'b) struct \<Rightarrow> ('a, 'c) struct \<Rightarrow> ('b \<Rightarrow> 'c) set" where
  "strong_hom \<A> \<B> \<equiv>
    let \<L> = lang \<A> in
    { h . h \<in> hom \<A> \<B> \<and> 
      (\<forall>m. \<forall>r \<in> \<L>\<^sup>R m. \<forall>l \<in> \<A>\<^sup>m. l \<in> rel_interp \<A> r \<longleftrightarrow> (map h l) \<in> rel_interp \<B> r) }"

definition all :: "bool list \<Rightarrow> bool" where
  "all bs \<equiv> foldr (\<and>) bs True"
declare all_def[simp]

definition zipWith :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zipWith f as bs \<equiv> map f (zip as bs)"
declare zipWith_def[simp]

definition allRelated :: "'a list \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> 'b list \<Rightarrow> bool" ("_\<sim>\<^sup>__" ) where
  "xs \<sim>\<^sup>E ys \<equiv> (length xs = length ys) \<and> all (zipWith (\<lambda>p. p \<in> E) xs ys)"

definition congruence :: "('a, 'b) struct \<Rightarrow> ('b \<times> 'b) set set" where
  "congruence \<A> \<equiv>
    let \<L> = lang \<A> in
    { E . is_struct \<L> \<A> \<and> 
      (\<forall>m. \<forall>r \<in> \<L>\<^sup>R m. \<forall>l \<in> \<A>\<^sup>m. \<forall>k \<in> \<A>\<^sup>m. (l \<sim>\<^sup>E k) \<longrightarrow> (l \<in> rel_interp \<A> r \<longleftrightarrow> k \<in> rel_interp \<A> r)) \<and>
      (\<forall>n. \<forall>f \<in> \<L>\<^sup>F n. \<forall>l \<in> \<A>\<^sup>n. \<forall>k \<in> \<A>\<^sup>n. (l \<sim>\<^sup>E k) \<longrightarrow> (fun_interp \<A> f l, fun_interp \<A> f k) \<in> E) }"

definition func_induced_equiv :: "('b \<Rightarrow> 'c) \<Rightarrow> ('b \<times> 'b) set" ("\<sim>\<^sub>_") where
  "\<sim>\<^sub>h \<equiv> { (a, b) . h a = h b }"

lemma [simp]: "(p \<in> \<sim>\<^sub>h) = (h (fst p) = h (snd p))"
  by (auto simp: func_induced_equiv_def)

lemma nonempty_elem[simp]: "Suc n = length xs \<Longrightarrow> \<exists>a ys. xs = a # ys"
  by (induction xs, auto)

lemma strong_hom_induced_all_related_is_eq:
  "\<lbrakk> E = \<sim>\<^sub>h \<rbrakk> \<Longrightarrow> \<forall>l. \<forall>k. (l \<sim>\<^sup>E k) \<longrightarrow> map h l = map h k"
  apply (rule allI)
  apply (induct_tac l)
   apply (simp add: allRelated_def)
  apply (rule allI)
  apply (rule impI)
  apply simp
  apply (erule_tac x = "tl k" in allE)
  apply (clarsimp simp: allRelated_def)
  apply auto
  by (frule nonempty_elem, erule exE, erule exE, simp)+

lemma [simp]: "\<lbrakk> E = \<sim>\<^sub>h ; l \<sim>\<^sup>E k \<rbrakk> \<Longrightarrow> map h l = map h k"
  by (drule strong_hom_induced_all_related_is_eq, auto)

(*
lemma "\<lbrakk> E = \<sim>\<^sub>h ; l \<sim>\<^sup>E k \<rbrakk> \<Longrightarrow> map h l = map h k"
proof(induction l arbitrary: k)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have IH: "(Suc (length l) = length k) \<and> (l \<sim>\<^sup>E (tl k)) \<and> map h l = map h (tl k)" by simp
  then show ?case 
  proof (cases k)
    case Nil
    then have mapKMt: "map h k = []" by simp
    then have "map h (a # l) = []" 
  next
    case (Cons a list)
    then show ?thesis sorry
  qed
qed *)

lemma strong_hom_induced_equiv_is_congr: "\<lbrakk> h \<in> strong_hom \<A> \<B> \<rbrakk> \<Longrightarrow> (\<sim>\<^sub>h) \<in> congruence \<A>"
  by (auto simp: strong_hom_def hom_def congruence_def)

end