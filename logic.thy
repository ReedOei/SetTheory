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
                    (\<forall>m. \<forall>r \<in> \<L>\<^sup>R m. rel_interp \<A> r \<subseteq> (\<A>\<^sup>m)) \<and>
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
(* declare zipWith_def[simp] *)

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

lemma nonempty_elem: "Suc n = length xs \<Longrightarrow> \<exists>a ys. xs = a # ys"
  by (induction xs, auto)

lemma induced_equiv_map_eq[dest]:
  fixes l and k and h 
  assumes all_equiv: "l \<sim>\<^sup>\<sim>\<^sub>h k"
  shows "map h l = map h k"
  using all_equiv
proof(induction l arbitrary: k)
  case Nil
  then have "k = []" by (auto simp: allRelated_def)
  then show ?case by auto
next
  case (Cons a l)
  then have equiv: "(a # l) \<sim>\<^sup>\<sim>\<^sub>h k" 
        and IH: "\<lbrakk> l \<sim>\<^sup>\<sim>\<^sub>h (tl k) \<rbrakk> \<Longrightarrow> map h l = map h (tl k)" by auto

  then have ex: "\<exists>b j. k = b # j"
  proof -
    from equiv have "Suc (length l) = length k" by (simp add: allRelated_def)
    thus ?thesis by (frule nonempty_elem)
  qed

  then obtain b where "\<exists>j. k = b # j" ..
  then obtain j where eq: "k = b # j" ..         

  then have tl_eq: "map h l = map h (tl k)"
  proof -
    from equiv and eq have "l \<sim>\<^sup>\<sim>\<^sub>h (tl k)" by (simp add: allRelated_def, auto simp: zipWith_def)
    from this and IH show ?thesis by simp
  qed

  from equiv and eq and tl_eq show ?case by (simp add: allRelated_def, auto simp: zipWith_def)
qed

lemma strong_hom_induced_equiv_is_congr: "\<lbrakk> h \<in> strong_hom \<A> \<B> \<rbrakk> \<Longrightarrow> (\<sim>\<^sub>h) \<in> congruence \<A>"
  by (auto simp: strong_hom_def hom_def congruence_def)

definition equiv_class :: "'b \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> 'b set" ("[_]\<^sub>_") where
  "[x]\<^sub>E \<equiv> {y . (x, y) \<in> E}"

definition bin_rel :: "'b set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> bool" where
  "bin_rel A E \<equiv> (\<forall>(x,y) \<in> E. x \<in> A \<and> y \<in> A)"

definition refl_rel :: "'b set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> bool" where
  "refl_rel A E \<equiv> bin_rel A E \<and> (\<forall>x. (x,x) \<in> E)"

definition sym_rel :: "'b set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> bool" where
  "sym_rel A E \<equiv> bin_rel A E \<and> (\<forall>x y. (x, y) \<in> E \<longleftrightarrow> (y, x) \<in> E)"

definition trans_rel :: "'b set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> bool" where
  "trans_rel A E \<equiv> bin_rel A E \<and> (\<forall>x y z. ((x,y) \<in> E \<and> (y, z) \<in> E) \<longrightarrow> (x, z) \<in> E)"

definition equiv_rel :: "'b set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> bool" where
  "equiv_rel A E \<equiv> bin_rel A E \<and> refl_rel A E \<and> sym_rel A E \<and> trans_rel A E"

lemma equiv_rel_refl:
  fixes A and E and x
  assumes "equiv_rel A E"
    shows "(x, x) \<in> E"
  using assms
  by (simp add: equiv_rel_def refl_rel_def)

lemma equiv_rel_sym:
  fixes A and E and x and y
  assumes "equiv_rel A E" and "(x, y) \<in> E"
    shows "(y, x) \<in> E"
  using assms
  by (simp add: equiv_rel_def sym_rel_def)

lemma equiv_rel_trans:
  fixes A and E and x and y and z
  assumes "equiv_rel A E" and "(x, y) \<in> E" and "(y, z) \<in> E"
    shows "(x, z) \<in> E"
  using assms
  apply (simp add: equiv_rel_def)
  apply (unfold trans_rel_def)
  apply (erule conjE)+
  apply (erule allE)+
  by auto

lemma equiv_class_sym:
  fixes A and E and x and y
  assumes "equiv_rel A E" and "x \<in> [y]\<^sub>E"
  shows "(x,y) \<in> E"     
  using assms
  apply (auto simp: equiv_class_def)
  by (erule equiv_rel_sym)

definition quotient_by_rel :: "'b set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> 'b set set" where
  "quotient_by_rel A E \<equiv> { C . \<exists>x \<in> A. C = [x]\<^sub>E }"

lemma uniq_eq_class:
  fixes A and E and C and x
  assumes eq_rel: "equiv_rel A E"
      and c: "C \<in> quotient_by_rel A E"
      and cx: "x \<in> C"
    shows "C = [x]\<^sub>E"
proof
  from eq_rel and c obtain z where z: "C = [z]\<^sub>E" by (auto simp: quotient_by_rel_def)
  from cx and z have xinz: "x \<in> [z]\<^sub>E" by simp
  from eq_rel and xinz have xz: "(x, z) \<in> E" by (rule equiv_class_sym)

  show "C \<subseteq> [x]\<^sub>E"
  proof
    fix y assume cy: "y \<in> C" show "y \<in> [x]\<^sub>E"
    proof(simp add: equiv_class_def)  
      from z and cy have zy: "(z, y) \<in> E" by (simp add: equiv_class_def)
      from eq_rel and xz and zy show "(x, y) \<in> E" by (rule equiv_rel_trans)
    qed
  qed

  show "([x]\<^sub>E) \<subseteq> C"
  proof
    fix y assume yinx: "y \<in> [x]\<^sub>E" show "y \<in> C"
      using z 
    proof(simp)
      from eq_rel and yinx have yx: "(y, x) \<in> E" by (rule equiv_class_sym)
      from eq_rel and yx and xz have "(y, z) \<in> E" by (rule equiv_rel_trans)
      from eq_rel and this have "(z, y) \<in> E" by (rule equiv_rel_sym)
      then show "y \<in> [z]\<^sub>E" by (simp add: equiv_class_def)
    qed
  qed
qed

lemma 
  fixes A and E
  assumes eq_rel: "equiv_rel A E"
  shows "\<forall>x \<in> A. \<exists>!C \<in> quotient_by_rel A E. x \<in> C" 
proof
  fix x
  assume xa: "x \<in> A"
  show "\<exists>!C \<in> quotient_by_rel A E. x \<in> C"
  proof -
    from xa and eq_rel have "x \<in> ([x]\<^sub>E) \<and> ([x]\<^sub>E) \<in> quotient_by_rel A E"
      by (auto simp: equiv_class_def quotient_by_rel_def equiv_rel_refl)

    then obtain C where c: "C \<in> quotient_by_rel A E \<and> x \<in> C" by auto
    then show ?thesis
    proof(rule ex1I)
      fix D
      assume d: "D \<in> quotient_by_rel A E \<and> x \<in> D"
      show "D = C"
      proof -
        from eq_rel and c and d have "D = [x]\<^sub>E" and "C = [x]\<^sub>E" by (auto simp: uniq_eq_class)
        thus "D = C" by simp
      qed
    qed
  qed
qed

lemma not_all_has_false:
  fixes l
  assumes "\<not> foldr (\<and>) l True"
  shows "\<exists>p s. l = p @ (False # s)"
  using assms
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then have IH: "\<not> foldr (\<and>) l True \<Longrightarrow> \<exists>p s. l = p @ False # s" and
             p: "\<not> foldr (\<and>) (a # l) True" by auto
  then show ?case
  proof(cases a)
    case True
    from this have a: "a" by simp
    from IH and p and a have "\<exists>p s. l = p @ False # s" by simp
    then obtain p where "\<exists>s. l = p @ False # s" ..
    then obtain s where eq: "l = p @ False # s" ..
    from a and eq show ?thesis
      apply simp
      apply (rule exI[where x = "True # p"])
      apply (rule exI[where x = "s"])
      by auto
  next
    case False
    then show ?thesis 
      apply simp
      apply (rule exI[where x = "[]"])
      apply (rule exI[where x = "l"])
      by auto
  qed
qed

lemma 
  fixes l :: "'b set list"
  assumes "l \<noteq> []"
  shows "(\<exists>k :: 'b list. length k = length l \<and> all (zipWith (\<lambda>(x, y). x \<in> y) k l)) \<or> {} \<in> list.set l"
  using assms
proof(clarsimp, induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have IH: "\<lbrakk>l \<noteq> []; {} \<notin> set l\<rbrakk> \<Longrightarrow> \<exists>k. length k = length l \<and> foldr (\<and>) (zipWith (\<lambda>(a, b). a \<in> b) k l) True" 
        and ne: "{} \<notin> set (a # l)" 
        and nea: "{} \<noteq> a" by auto
  then obtain x where xa: "x \<in> a" by auto
  from IH and ne show ?case 
    apply clarsimp
    apply (cases l)
  proof(simp)
    assume "l = []"
    show "\<exists>k. length k = Suc 0 \<and> foldr (\<and>) (zipWith (\<lambda>(x, y). x \<in> y) k [a]) True"
    proof(rule exI[where x = "[x]"], auto simp: zipWith_def)
      from xa show "x \<in> a" by auto
    qed
  next
    fix b k
    assume l: "l = b # k"
    from l and ne and IH have "\<exists>k. length k = length l \<and> foldr (\<and>) (zipWith (\<lambda>(a, b). a \<in> b) k l) True" by auto
    then obtain kl where kl: "length kl = length l \<and> foldr (\<and>) (zipWith (\<lambda>(a, b). a \<in> b) kl l) True" ..
    show "\<exists>k. length k = Suc (length l) \<and> foldr (\<and>) (zipWith (\<lambda>(x, y). x \<in> y) k (a # l)) True"
    proof(rule exI[where x = "x # kl"], auto)
      from kl show "length kl = length l" by auto
      from xa and kl show "foldr (\<and>) (zipWith (\<lambda>(x, y). x \<in> y) (x # kl) (a # l)) True" by (auto simp: zipWith_def)
    qed
  qed
qed

definition quotient_rel_interp :: "'b list set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> 'b set list set" where
  "quotient_rel_interp r E \<equiv> { elems. (map (\<lambda>a. (SOME x. x \<in> a)) elems) \<in> r }"

definition quotient_fun_interp :: "('b list \<Rightarrow> 'b) \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> 'b set list \<Rightarrow> 'b set" where
  "quotient_fun_interp f E elems \<equiv> [ f (map (\<lambda>a. (SOME x. x \<in> a)) elems) ]\<^sub>E"

definition quotient_struct :: "('a, 'b) struct \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> ('a, 'b set) struct" where
  "quotient_struct \<A> E \<equiv> \<lparr> lang = lang \<A>, underlying = quotient_by_rel (\<A>\<^sup>U) E,
                            rel_interp = \<lambda>r. quotient_rel_interp (rel_interp \<A> r) E,
                            fun_interp = \<lambda>f. quotient_fun_interp (fun_interp \<A> f) E \<rparr>"

lemma rel_subset:
  fixes \<A> and r and m
  assumes a_struct: "is_struct (lang \<A>) \<A>" and
          rel: "r \<in> ((lang \<A>)\<^sup>R) m"
  shows "rel_interp \<A> r \<subseteq> (\<A>\<^sup>m)"
  using assms
  by (auto simp: is_struct_def)

thm someI
thm someI_ex
thm some_eq_ex
thm some_in_eq

lemma 
  fixes y z
  assumes "(SOME x. x \<in> y) \<in> z"
  shows "y \<noteq> {}"
  using assms 
proof(auto simp: some_in_eq)
  assume sin: "(SOME x. False) \<in> z" and ymt: "y = {}"
  show "False"
  proof -
    from sin have "False"
      apply (rule someI)

lemma
  fixes \<A> and E
  assumes a_struct: "is_struct (lang \<A>) \<A>"
  shows "is_struct (lang \<A>) (quotient_struct \<A> E)"
  using assms
proof(auto simp: is_struct_def tuples_def 
                 quotient_struct_def quotient_by_rel_def 
                 quotient_rel_interp_def quotient_fun_interp_def)
  fix m r x y
  assume rel: "r \<in> ((lang \<A>)\<^sup>R) m" and 
         in_rel: "map (\<lambda>a. SOME x. x \<in> a) x \<in> rel_interp \<A> r" and
         in_set: "y \<in> list.set x"

  from a_struct and rel have r_sub: "rel_interp \<A> r \<subseteq> (\<A>\<^sup>m)" by (rule rel_subset)
  from r_sub and in_rel have "map (\<lambda>a. SOME x. x \<in> a) x \<in> (\<A>\<^sup>m)" by auto "
  from in_rel and in_set have "y \<noteq> {}"
  then show "y \<in> (\<A>\<^sup>U)"
  then obtain x where "x \<in> (\<A>\<^sup>U) \<and> y = [x]\<^sub>E"
  proof -


lemma 
  fixes \<A> and E
  shows "(\<lambda>a. [a]\<^sub>E) \<in> strong_hom \<A> (quotient_struct \<A> E)"

end