(*<*)
\<comment>\<open> ******************************************************************** 
 * This file contains missing results from HOL-CSP,
   lemmas for the behaviour of Interrupt with Sequential Composition,
   and projections of particular processes defined using iterate.
 ******************************************************************************\<close>
(*>*)
theory "HOL-CSP_Add_Ons"
  imports "HOL-CSP_RS"
begin

no_notation Cons  ("_ ⋅/ _" [66,65] 65)

section \<open>Notation for write Operator\<close>

text \<open>The notation defined in \<^session>\<open>HOL-CSP\<close> for \<^const>\<open>write\<close> is \<^term>\<open>c\<^bold>!a \<rightarrow> P\<close>.
We introduce a new notation.\<close>

notation "write" (\<open>(3(_\<^bold>._) /\<rightarrow> _)\<close> [0,0,78] 78)

lemma \<open>c\<^bold>.a \<rightarrow> P = c\<^bold>!a \<rightarrow> P\<close> ..



section \<open>Missing Lemmas\<close>

text \<open>We give here some results that should definitively be part of \<^session>\<open>HOL-CSP\<close>.\<close>

text \<open>The three following lemmas already exist in the library HOL-CSP,
but with the wrong type on channel \<^term>\<open>c\<close> (\<^typ>\<open>'a \<Rightarrow> 'a\<close> instead of \<^typ>\<open>'a \<Rightarrow> 'b\<close>).\<close>

lemma initials_write :      \<open>(c\<^bold>!a \<rightarrow> Q)\<^sup>0     = {ev (c a)}\<close>
  and initials_read :       \<open>(c\<^bold>?a\<in>A \<rightarrow> P a)\<^sup>0 = ev ` c ` A\<close>
  and initials_ndet_write : \<open>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)\<^sup>0 = ev ` c ` A\<close>
  by (auto simp add: initials_def write_projs read_projs ndet_write_projs)


corollary no_initial_tick_write :  \<open>(c\<^bold>!a \<rightarrow> Q)\<^sup>0 \<inter> range tick = {}\<close>
  and no_initial_tick_read :       \<open>(c\<^bold>?a \<rightarrow> P a)\<^sup>0 \<inter> range tick = {}\<close>
  and no_initial_tick_ndet_write : \<open>(c\<^bold>!\<^bold>!a \<rightarrow> P a)\<^sup>0 \<inter> range tick = {}\<close>
  by (auto simp add: initials_write0 initials_write initials_read initials_ndet_write)

lemma no_initial_tick_write0 : \<open>(a \<rightarrow> Q)\<^sup>0 \<inter> range tick = {}\<close>
  by (auto simp add: initials_write0 initials_write initials_read initials_ndet_write)


lemma tickFree_iff_set_range_ev : \<open>tickFree t \<longleftrightarrow> set t \<subseteq> range ev\<close>
  by (induct t) (auto simp add: is_ev_def)

lemma GlobalDet_is_STOP_iff : \<open>\<box>a \<in> A. P a = STOP \<longleftrightarrow> (\<forall>a \<in> A. P a = STOP)\<close>
  by (simp add: STOP_iff_T T_GlobalDet, safe, auto)

lemma mono_Det_FD_same_lhs :
  \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D R \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<box> R\<close>
  by (fact mono_Det_FD[of P Q P R, simplified])

lemma mono_GlobalDet_FD_const:
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D \<box>a \<in> A. Q a\<close>
  by (metis GlobalDet_id mono_GlobalDet_FD)



section \<open>Interrupt and Sequential Composition\<close>

subsection \<open>Main Theorem\<close>

theorem non_terminating_Interrupt_Seq :
  \<open>(P \<triangle> Q) \<^bold>; R = P \<triangle> (Q \<^bold>; R)\<close> (is \<open>?lhs = ?rhs\<close>)
  if \<open>non_terminating P\<close> and \<open>Q\<^sup>0 \<inter> range tick = {}\<close>
proof -
  have non_ter [simp] : \<open>t @ [\<checkmark>(r)] \<in> \<T> P \<longleftrightarrow> False\<close> for t r
    by (metis \<open>non_terminating P\<close> non_terminating_is_right non_tickFree_tick tickFree_append_iff)
  have not_tick_init : \<open>[\<checkmark>(r)] \<in> \<T> Q \<longleftrightarrow> False\<close> for r
    by (meson disjoint_iff initials_memI rangeI \<open>Q\<^sup>0 \<inter> range tick = {}\<close>)
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then consider \<open>t \<in> \<D> P\<close> | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close> \<open>v \<in> \<D> Q\<close>
      | u v r u1 u2 where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> \<open>tF u1\<close> \<open>u2 \<in> \<T> Q\<close> \<open>v \<in> \<D> R\<close>
      by (auto simp add: D_Seq Interrupt_projs)
    thus \<open>t \<in> \<D> ?rhs\<close>
    proof cases
      show \<open>t \<in> \<D> P \<Longrightarrow> t \<in> \<D> ?rhs\<close> by (simp add: D_Seq D_Interrupt)
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> tF u \<Longrightarrow> v \<in> \<D> Q \<Longrightarrow> t \<in> \<D> ?rhs\<close> for u v
        by (auto simp add: D_Interrupt D_Seq)
    next
      fix u v r u1 u2 assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close>
        \<open>u1 \<in> \<T> P\<close> \<open>tF u1\<close> \<open>u2 \<in> \<T> Q\<close> \<open>v \<in> \<D> R\<close>
      from this(2, 4, 5) obtain u2'
        where \<open>u = u1 @ u2'\<close> \<open>u2 = u2' @ [\<checkmark>(r)]\<close>
        by (metis (no_types) T_nonTickFree_imp_decomp append.assoc
            append1_eq_conv non_tickFree_tick tickFree_append_iff)
      with \<open>tF u1\<close> \<open>u1 \<in> \<T> P\<close> \<open>u2 \<in> \<T> Q\<close> \<open>v \<in> \<D> R\<close> show \<open>t \<in> \<D> ?rhs\<close>
        by (simp add: \<open>t = u @ v\<close> D_Seq D_Interrupt) blast
    qed
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (simp add: Interrupt_projs Seq_projs) (metis append_assoc)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then consider \<open>(t, X \<union> range tick) \<in> \<F> (P \<triangle> Q)\<close> \<open>tF t\<close>
      | u r v where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)\<close> \<open>(v, X) \<in> \<F> R\<close>
      by (auto simp add: Seq_projs)
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      assume \<open>(t, X \<union> range tick) \<in> \<F> (P \<triangle> Q)\<close> \<open>tF t\<close>
      with \<open>t \<notin> \<D> ?lhs\<close> consider \<open>(t, X \<union> range tick) \<in> \<F> P\<close> \<open>tF t\<close> \<open>([], X \<union> range tick) \<in> \<F> Q\<close>
        | t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>tF t1\<close> \<open>(t2, X \<union> range tick) \<in> \<F> Q\<close> \<open>t2 \<noteq> []\<close>
        by (auto simp add: Interrupt_projs D_Seq)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      proof cases
        show \<open>\<lbrakk>(t, X \<union> range tick) \<in> \<F> P; tF t; ([], X \<union> range tick) \<in> \<F> Q\<rbrakk>
              \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
          by (auto simp add: F_Interrupt F_Seq intro: is_processT4)
      next
        show \<open>\<lbrakk>t = t1 @ t2; t1 \<in> \<T> P; tF t1; (t2, X \<union> range tick) \<in> \<F> Q; t2 \<noteq> []\<rbrakk>
              \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t1 t2
          by (use \<open>tF t\<close> in \<open>auto simp add: F_Interrupt F_Seq\<close>)
      qed
    next
      fix u r v assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)\<close> \<open>(v, X) \<in> \<F> R\<close>
      then obtain u1 u2 where \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> \<open>tF u1\<close> \<open>u2 \<in> \<T> Q\<close>
        by (auto simp add: T_Interrupt)
      from \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> obtain u2'
        where \<open>u2 = u2' @ [\<checkmark>(r)]\<close> \<open>u = u1 @ u2'\<close>
        by (metis append.right_neutral append_butlast_last_id
            butlast_append butlast_snoc last_appendR last_snoc non_ter)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Interrupt \<open>t = u @ v\<close> Seq_projs)
          (metis Nil_is_append_conv \<open>(v, X) \<in> \<F> R\<close> \<open>tF u1\<close> \<open>u @ [\<checkmark>(r)] = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> \<open>u2 \<in> \<T> Q\<close>
            append.right_neutral not_tick_init same_append_eq)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    then consider \<open>(t, X) \<in> \<F> P\<close> \<open>tF t\<close> \<open>([], X) \<in> \<F> (Q \<^bold>; R)\<close>
      | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close> \<open>(v, X) \<in> \<F> (Q \<^bold>; R)\<close> \<open>v \<noteq> []\<close>
      by (simp add: Interrupt_projs T_Seq Cons_eq_append_conv)
        (smt (verit, best) D_T is_processT3_TR_append not_tick_init self_append_conv2)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      show \<open>(t, X) \<in> \<F> P \<Longrightarrow> tF t \<Longrightarrow> ([], X) \<in> \<F> (Q \<^bold>; R) \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Seq F_Interrupt)
          (metis (mono_tags, lifting) F_T append.right_neutral f_inv_into_f
            is_processT5 non_ter not_tick_init)
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> tF u \<Longrightarrow> (v, X) \<in> \<F> (Q \<^bold>; R) \<Longrightarrow> v \<noteq> [] \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u v
        by (simp add: F_Seq Interrupt_projs)
          (smt (verit, best) append_assoc)
    qed
  qed
qed



subsection \<open>Corollaries\<close>

corollary non_terminating_Interrupt_Seq_Mprefix :
  \<open>non_terminating P \<Longrightarrow> P \<triangle> (\<box>a \<in> A \<rightarrow> Q a) \<^bold>; R = P \<triangle> (\<box>a \<in> A \<rightarrow> Q a \<^bold>; R)\<close>
  by (auto intro: non_terminating_Interrupt_Seq simp add: initials_Mprefix)

corollary non_terminating_Interrupt_Seq_Mndetprefix :
  \<open>non_terminating P \<Longrightarrow> P \<triangle> (\<sqinter>a \<in> A \<rightarrow> Q a) \<^bold>; R = P \<triangle> (\<sqinter>a \<in> A \<rightarrow> Q a \<^bold>; R)\<close>
  by (auto intro: non_terminating_Interrupt_Seq simp add: initials_Mndetprefix)

corollary non_terminating_Interrupt_Seq_write0 :
  \<open>non_terminating P \<Longrightarrow> P \<triangle> (a \<rightarrow> Q) \<^bold>; R = P \<triangle> (a \<rightarrow> Q \<^bold>; R)\<close>
  by (auto intro: non_terminating_Interrupt_Seq simp add: initials_write0)

corollary non_terminating_Interrupt_Seq_write :
  \<open>non_terminating P \<Longrightarrow> P \<triangle> (c\<^bold>!a \<rightarrow> Q) \<^bold>; R = P \<triangle> (c\<^bold>!a \<rightarrow> Q \<^bold>; R)\<close>
  by (auto intro: non_terminating_Interrupt_Seq simp add: initials_write)

corollary non_terminating_Interrupt_Seq_read :
  \<open>non_terminating P \<Longrightarrow> P \<triangle> (c\<^bold>?a\<in>A \<rightarrow> Q a) \<^bold>; R = P \<triangle> (c\<^bold>?a\<in>A \<rightarrow> Q a \<^bold>; R)\<close>
  by (auto intro: non_terminating_Interrupt_Seq simp add: initials_read)

corollary non_terminating_Interrupt_Seq_ndet_write :
  \<open>non_terminating P \<Longrightarrow> P \<triangle> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a) \<^bold>; R = P \<triangle> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a \<^bold>; R)\<close>
  by (auto intro: non_terminating_Interrupt_Seq simp add: initials_ndet_write)





section \<open>Projections of Particular Processes Obtained via \<^const>\<open>iterate\<close>\<close>

text \<open>This will be useful for some denotational proofs later.\<close>

subsection \<open>Projections of \<^term>\<open>iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>P\<close>\<close>

lemma F_iterate_Mndetprefix :
  \<open>\<F> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>P) =
   (if A = {} then if i = 0 then \<F> P else {(s, X). s = []} else
   {(s, X). set s \<subseteq> ev ` A \<and> length s < i \<and> (\<exists>a \<in> A. ev a \<notin> X)} \<union>
   {(s @ t, X)| s t X. set s \<subseteq> ev ` A \<and> length s = i \<and> (t, X) \<in> \<F> P})\<close>
  (is \<open>?lhs P i = (if A = {} then if i = 0 then \<F> P else {(s, X). s = []} else
                   ?rhs1 P i \<union> ?rhs2 P i)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs P i = (if i = 0 then \<F> P else {(s, X). s = []})\<close>
    by (cases i) (simp_all add: F_STOP)
next
  show \<open>?lhs P i = ?rhs1 P i \<union> ?rhs2 P i\<close> if \<open>A \<noteq> {}\<close>
  proof (induct i arbitrary: P)
    show \<open>?lhs P 0 = ?rhs1 P 0 \<union> ?rhs2 P 0\<close> for P by simp
  next
    fix i P assume * : \<open>?lhs P i = ?rhs1 P i \<union> ?rhs2 P i\<close> for P
    let ?tmp = \<open>{(s, X). set s \<subseteq> ev ` A \<and> length s = i \<and> (\<exists>a \<in> A. ev a \<notin> X)}\<close>
    have \<open>?lhs P (Suc i) = ?lhs (\<sqinter>a\<in>A \<rightarrow> P) i\<close>
      by (simp del: iterate_Suc add: iterate_Suc2)
    also from "*" have \<open>\<dots> = ?rhs1 (\<sqinter>a\<in>A \<rightarrow> P) i \<union> ?rhs2 (\<sqinter>a\<in>A \<rightarrow> P) i\<close> .
    also have \<open>\<dots> = ?rhs1 P (Suc i) \<union> ?rhs2 P (Suc i)\<close>
    proof -
      have \<open>?rhs2 (\<sqinter>a\<in>A \<rightarrow> P) i = ?rhs2 P (Suc i) \<union> ?tmp\<close>
      proof (intro subset_antisym subsetI)
        fix s_X assume \<open>s_X \<in> ?rhs2 (\<sqinter>a \<in> A \<rightarrow> P) i\<close>
        then obtain t u X
          where ** : \<open>s_X = (t @ u, X)\<close> \<open>set t \<subseteq> ev ` A\<close>
                    \<open>length t = i\<close> \<open>(u, X) \<in> \<F> (\<sqinter>a \<in> A \<rightarrow> P)\<close> by blast
        from "**"(4) consider a where \<open>a \<in> A\<close> \<open>u = []\<close> \<open>ev a \<notin> X\<close>
          | a u' where \<open>a \<in> A\<close> \<open>u = ev a # u'\<close> \<open>(u', X) \<in> \<F> P\<close>
          by (auto simp add: Mndetprefix_projs \<open>A \<noteq> {}\<close>)
        thus \<open>s_X \<in> ?rhs2 P (Suc i) \<union> ?tmp\<close>
        proof cases
          show \<open>a \<in> A \<Longrightarrow> u = [] \<Longrightarrow> ev a \<notin> X \<Longrightarrow> s_X \<in> ?rhs2 P (Suc i) \<union> ?tmp\<close> for a
            using "**"(2) by (auto simp add: "**"(1, 3) subset_iff)
        next
          fix a u' assume \<open>a \<in> A\<close> \<open>u = ev a # u'\<close> \<open>(u', X) \<in> \<F> P\<close>
          hence \<open>set (t @ [ev a]) \<subseteq> ev ` A\<close> \<open>length (t @ [ev a]) = Suc i\<close>
                \<open>s_X = ((t @ [ev a]) @ u', X)\<close>
            by (simp_all add: "**"(1, 2, 3))
          with \<open>(u', X) \<in> \<F> P\<close> show \<open>s_X \<in> ?rhs2 P (Suc i) \<union> ?tmp\<close> by blast
        qed
      next
        fix s_X assume \<open>s_X \<in> ?rhs2 P (Suc i) \<union> ?tmp\<close>
        then consider t u X where \<open>s_X = (t @ u, X)\<close> \<open>set t \<subseteq> ev ` A\<close> \<open>length t = Suc i\<close> \<open>(u, X) \<in> \<F> P\<close>
          | s X a where \<open>s_X = (s, X)\<close> \<open>a \<in> A\<close> \<open>set s \<subseteq> ev ` A\<close> \<open>length s = i\<close> \<open>ev a \<notin> X\<close> by auto
        thus \<open>s_X \<in> ?rhs2 (\<sqinter>a \<in> A \<rightarrow> P) i\<close>
        proof cases
          fix t u X assume ** : \<open>s_X = (t @ u, X)\<close> \<open>set t \<subseteq> ev ` A\<close> \<open>length t = Suc i\<close> \<open>(u, X) \<in> \<F> P\<close>
          from "**"(2, 3) obtain a t' where \<open>a \<in> A\<close> \<open>t = t' @ [ev a]\<close> \<open>set t' \<subseteq> ev ` A\<close> \<open>length t' = i\<close>
            by (cases t rule: rev_cases) auto
          moreover from this(2) "**"(1) have \<open>s_X = (t' @ ev a # u, X)\<close> by simp
          moreover have \<open>(ev a # u, X) \<in> \<F> (\<sqinter>a\<in>A \<rightarrow> P)\<close>
            by (simp add: F_Mndetprefix write0_def F_Mprefix \<open>A \<noteq> {}\<close> "**"(4) \<open>a \<in> A\<close>)
          ultimately show \<open>s_X \<in> ?rhs2 (\<sqinter>a \<in> A \<rightarrow> P) i\<close> by blast
        next
          show \<open>\<lbrakk>s_X = (s, X); a \<in> A; set s \<subseteq> ev ` A; length s = i; ev a \<notin> X\<rbrakk>
                \<Longrightarrow> s_X \<in> ?rhs2 (\<sqinter>a \<in> A \<rightarrow> P) i\<close> for s X a
            by (auto simp add: F_Mndetprefix write0_def F_Mprefix)
        qed
      qed
      moreover have \<open>?rhs1 (\<sqinter>a\<in>A \<rightarrow> P) i \<union> ?tmp = ?rhs1 P (Suc i)\<close>by auto
      ultimately show \<open>?rhs1 (\<sqinter>a\<in>A \<rightarrow> P) i \<union> ?rhs2 (\<sqinter>a\<in>A \<rightarrow> P) i =
                       ?rhs1 P (Suc i) \<union> ?rhs2 P (Suc i)\<close> by auto
    qed
    finally show \<open>?lhs P (Suc i) = ?rhs1 P (Suc i) \<union> ?rhs2 P (Suc i)\<close> .
  qed
qed


corollary T_iterate_Mndetprefix :
  \<open>\<T> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>P) =
   (if A = {} then if i = 0 then \<T> P else {[]}
    else {s. set s \<subseteq> ev ` A \<and> length s < i} \<union>
         {s @ t| s t. set s \<subseteq> ev ` A \<and> length s = i \<and> t \<in> \<T> P})\<close>
  unfolding set_eq_iff
  by (auto simp add: F_iterate_Mndetprefix T_F_spec[symmetric])


lemma D_iterate_Mndetprefix :
  \<open>\<D> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>P) =
   (if A = {} then if i = 0 then \<D> P else {}
    else {s @ t| s t. set s \<subseteq> ev ` A \<and> length s = i \<and> t \<in> \<D> P})\<close>
  (is \<open>?lhs P i = (if A = {} then if i = 0 then \<D> P else {} else ?rhs P i)\<close>)
  for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs P i = (if i = 0 then \<D> P else {})\<close>
    by (cases i) (simp_all add: D_STOP)
next
  show \<open>?lhs P i = ?rhs P i\<close> if \<open>A \<noteq> {}\<close>
  proof (induct i arbitrary: P)
    show \<open>?lhs P 0 = ?rhs P 0\<close> for P by simp
  next
    fix i P assume * : \<open>?lhs P i = ?rhs P i\<close> for P
    have \<open>?lhs P (Suc i) = ?lhs (\<sqinter>a \<in> A \<rightarrow> P) i\<close>
      by (simp del: iterate_Suc add: iterate_Suc2)
    also from "*" have \<open>\<dots> = ?rhs (\<sqinter>a \<in> A \<rightarrow> P) i\<close> .
    also have \<open>\<dots> = ?rhs P (Suc i)\<close>
    proof safe
      fix s t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume \<open>set s \<subseteq> ev ` A\<close> \<open>t \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close> \<open>i = length s\<close>
      from \<open>t \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close>
      obtain a t' where \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>t' \<in> \<D> P\<close>
        by (auto simp add: D_Mndetprefix write0_def D_Mprefix \<open>A \<noteq> {}\<close>)
      from this(1, 2) have \<open>s @ t = (s @ [ev a]) @ t'\<close> \<open>set (s @ [ev a]) \<subseteq> ev ` A\<close>
                           \<open>length (s @ [ev a]) = Suc (length s)\<close>
        by (simp_all add: \<open>set s \<subseteq> ev ` A\<close>)
      with \<open>t' \<in> \<D> P\<close> show \<open>\<exists>s' t'. s @ t = s' @ t' \<and> set s' \<subseteq> ev ` A \<and>
                                     length s' = Suc (length s) \<and> t' \<in> \<D> P\<close> by blast
    next
      fix s t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
      assume \<open>set s \<subseteq> ev ` A\<close> \<open>length s = Suc i\<close> \<open>t \<in> \<D> P\<close>
      from this(1, 2) obtain a s'
        where \<open>a \<in> A\<close> \<open>s = s' @ [ev a]\<close> \<open>set s' \<subseteq> ev ` A\<close> \<open>length s' = i\<close>
        by (cases s rule: rev_cases) auto
      from this(1, 2) \<open>t \<in> \<D> P\<close> have \<open>s @ t = s' @ ev a # t\<close> \<open>ev a # t \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close>
        by (simp_all add: D_Mndetprefix write0_def D_Mprefix \<open>A \<noteq> {}\<close>)
      with \<open>set s' \<subseteq> ev ` A\<close> \<open>length s' = i\<close> 
      show \<open>\<exists>s' t'. s @ t = s' @ t' \<and> set s' \<subseteq> ev ` A \<and>
                    length s' = i \<and> t' \<in> \<D> (\<sqinter>a\<in>A \<rightarrow> P)\<close> by blast
    qed
    finally show \<open>?lhs P (Suc i) = ?rhs P (Suc i)\<close> .
  qed
qed



subsection \<open>Projections of \<^term>\<open>iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P\<close>\<close>

corollary F_iterate_Mndetprefix_UNIV :
  \<open>\<F> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P) =
   {(s, X). tF s \<and> length s < i \<and> (\<exists>a. ev a \<notin> X)} \<union>
   {(s @ t, X) |s t X. tF s \<and> length s = i \<and> (t, X) \<in> \<F> P}\<close>
  by (simp add: F_iterate_Mndetprefix tickFree_iff_set_range_ev)

corollary T_iterate_Mndetprefix_UNIV :
  \<open>\<T> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow>  X)\<cdot>P) =
   {s. tF s \<and> length s < i} \<union> {s @ t |s t. tF s \<and> length s = i \<and> t \<in> \<T> P}\<close>
  by (simp add: T_iterate_Mndetprefix tickFree_iff_set_range_ev)

corollary D_iterate_Mndetprefix_UNIV :
  \<open>\<D> (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>P) = {s @ t |s t. tF s \<and> length s = i \<and> t \<in> \<D> P}\<close>
  by (simp add: D_iterate_Mndetprefix tickFree_iff_set_range_ev)



subsection \<open>Projections of \<^term>\<open>\<sqinter> j \<in> {..<i}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV)\<close>\<close>

lemma F_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV :
  \<open>\<F> (\<sqinter> j \<in> {..<i}. (iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>(UNIV :: 'a set) \<rightarrow> X)\<cdot>(SKIPS (UNIV :: 'r set)))) =
   (if i = 0 then {(t, X). t = []} else
    {(t, X). tF t \<and> length t < i - 1 \<and> (\<exists>a. ev a \<notin> X)} \<union>
    {(t, X) |t X. tF t \<and> length t < i \<and> (\<exists>r. \<checkmark>(r) \<notin> X)} \<union>
    {(t @ [\<checkmark>(r)], X) |t r X. tF t \<and> length t < i})\<close>
proof -
  define S  :: \<open>nat \<Rightarrow> ('a, 'r) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
    where \<open>S  \<equiv> \<lambda>j. \<F> (iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV))\<close>
  define S1 :: \<open>nat \<Rightarrow> ('a, 'r) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
    where \<open>S1 \<equiv> \<lambda>j. {(t, X). tF t \<and> length t < j \<and> (\<exists>a. ev a \<notin> X)}\<close>
  define S2 :: \<open>nat \<Rightarrow> ('a, 'r) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
    where \<open>S2 \<equiv> \<lambda>j. {(t, X) |t X. tF t \<and> length t = j \<and> (\<exists>r. \<checkmark>(r) \<notin> X)}\<close>
  define S3 :: \<open>nat \<Rightarrow> ('a, 'r) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
    where \<open>S3 \<equiv> \<lambda>j. {(t @ [\<checkmark>(r)], X) |t r X. tF t \<and> length t = j}\<close>
  have \<open>S j = S1 j \<union> S2 j \<union> S3 j\<close> for j
    by (auto simp add: F_iterate_Mndetprefix_UNIV F_SKIPS S_def S1_def S2_def S3_def)
    
  hence \<open>(\<Union>j \<in> {..<i}. S j) =
         (\<Union>j \<in> {..<i}. S1 j) \<union> (\<Union>j \<in> {..<i}. S2 j) \<union> (\<Union>j \<in> {..<i}. S3 j)\<close> by auto
  also have \<open>(\<Union>j \<in> {..<i}. S1 j) = {(t, X). tF t \<and> length t < i - 1 \<and> (\<exists>a. ev a \<notin> X)}\<close>
    by (force simp add: S1_def)
  also have \<open>(\<Union>j \<in> {..<i}. S2 j) = {(t, X) |t X. tF t \<and> length t < i \<and> (\<exists>r. \<checkmark>(r) \<notin> X)}\<close>
    by (auto simp add: S2_def)
  also have \<open>(\<Union>j \<in> {..<i}. S3 j) = {(t @ [\<checkmark>(r)], X) |t r X. tF t \<and> length t < i}\<close>
    by (auto simp add: S3_def)
  finally show ?thesis
    by (cases i, simp_all add: F_STOP F_GlobalNdet S_def)
      (use lessThan_Suc in \<open>auto simp add: S_def\<close>)
qed


lemma T_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV :
  \<open>\<T> (\<sqinter> j \<in> {..<i}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV)) =
   {[]} \<union> {t. tF t \<and> length t < i} \<union> {t @ [\<checkmark>(r)] |t r. tF t \<and> length t < i}\<close>
proof -
  have * : \<open>\<And>P. \<T> P = {t. \<exists>X. (t, X) \<in> \<F> P}\<close> using F_T T_F_spec by blast
  show ?thesis
    by (auto simp add: "*" F_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV)
qed


lemma D_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV :
  \<open>\<D> (\<sqinter> j \<in> {..<i}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV)) = {}\<close>
proof -
  have \<open>\<D> (iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV)) = {}\<close> for j
    by (induct j) (simp_all add: D_SKIPS D_Mndetprefix')
  thus \<open>\<D> (\<sqinter> j \<in> {..<i}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>UNIV \<rightarrow> X)\<cdot>(SKIPS UNIV)) = {}\<close>
    by (auto simp add: D_GlobalNdet)
qed




subsection \<open>Projections of \<^term>\<open>iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> SKIPS R)\<cdot>P\<close>\<close>

text \<open>We give an equality for \<^term>\<open>iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> SKIPS R)\<cdot>P\<close>.
With the previous lemmas, the projections can be recovered if needed.\<close>

lemma iterate_Mndetprefix_SKIPS_is :
  \<open>iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>A \<rightarrow> X) \<sqinter> SKIPS R)\<cdot>P =
   (if i = 0 then P else
    (iterate i\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>P) \<sqinter>
    (\<sqinter> j \<in> {..<i}. (iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R))))\<close>
proof (induct i)
  case 0 show ?case by simp
next
  case (Suc i)
  show ?case
  proof (cases i)
    show \<open>i = 0 \<Longrightarrow> ?case\<close> by (simp add: lessThan_Suc)
  next
    have * : \<open>nat.pred ` {0<..<Suc i'} = {..<i'}\<close> for i'
      by (force simp add: greaterThanLessThan_def lessThan_def image_iff less_Suc_eq_0_disj)
    have ** : \<open>inj_on nat.pred {0<..<Suc i'}\<close> for i'
      by (metis greaterThanLessThan_iff inj_on_inverseI less_nat_zero_code nat.exhaust_sel)
    have \<open>x \<in> {..<Suc i'} \<Longrightarrow> inv_into {0<..<Suc (Suc i')} nat.pred x = Suc x\<close> for i' x
      by (rule inv_into_f_eq[OF **]) auto
    hence *** : \<open>\<sqinter>x\<in>{..<Suc i'}. iterate (inv_into {0<..<Suc (Suc i')} nat.pred x)\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R) =
                 \<sqinter>x\<in>{..<Suc i'}. iterate (Suc x)\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)\<close> for i'
      by (metis (no_types, lifting) mono_GlobalNdet_eq)
    have $ : \<open>\<sqinter>a\<in>A \<rightarrow> \<sqinter>j\<in>{..<Suc i'}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R) =
              \<sqinter>j\<in>{0<..<Suc (Suc i')}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)\<close> for i'
      by (simp add: inj_on_mapping_over_GlobalNdet[OF **] * ***)
        (cases \<open>A = {}\<close>, simp_all add: Mndetprefix_distrib_GlobalNdet lessThan_Suc)
    have $$ : \<open>SKIPS R = \<sqinter>j\<in>{0}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)\<close> by simp
    have $$$ : \<open>(\<sqinter>a\<in>A \<rightarrow> \<sqinter>j\<in>{..<Suc i'}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)) \<sqinter> SKIPS R =
                \<sqinter>j\<in>{..<Suc (Suc i')}. iterate j\<cdot>(\<Lambda> X. \<sqinter>a\<in>A \<rightarrow> X)\<cdot>(SKIPS R)\<close> for i'
      by (subst $, subst $$, subst GlobalNdet_factorization_union)
        (auto, metis One_nat_def atLeast0LessThan atLeast0_lessThan_Suc_eq_insert_0
          atLeastLessThanSuc_atLeastAtMost atLeastSucLessThan_greaterThanLessThan image_Suc_lessThan)
    show ?case if \<open>i = Suc i'\<close> for i'
      by (unfold iterate_Suc Suc.hyps)
        (simp add: \<open>i = Suc i'\<close> Mndetprefix_distrib_Ndet $$$ flip: Ndet_assoc)
  qed
qed



end