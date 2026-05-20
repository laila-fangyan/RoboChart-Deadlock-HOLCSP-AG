\<comment>\<open> ******************************************************************** 
 * This file contains definitions and lemmas for \<open>Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>, \<open>GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close>
   and \<open>GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'\<close>.
   These operators lead to easier proofs of deadlock freedom,
   that can be automatised to some extent. 
 ******************************************************************************\<close>


theory Inductive_Deadlock_Freedom
  imports External_Choice_And_Guard "HOL-CSP_Add_Ons"
begin


section \<open>Establishing Deadlock Freedom through Iterations\<close>


subsection \<open>Definitions\<close>

text \<open>In short, the construction that we make here consist in prefixing a process
by iterations of the function \<^term>\<open>\<lambda>X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV\<close>.
We therefore introduce a shortcut for this.\<close>


definition Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ::
  \<open>nat \<Rightarrow> ('a, 'b) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<rightarrow> ('a, 'b) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i \<equiv> iterate i\<cdot>(\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV)\<close>


text \<open>We immediately derive its properties.\<close>

lemma Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_0 [simp] : \<open>Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 0 = (\<Lambda> X. X)\<close>
  by (simp add: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def cfun_eqI)

lemma Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Suc [simp] : \<open>Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Suc i) = (\<Lambda> X. (\<sqinter>a\<in>UNIV \<rightarrow> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>X) \<sqinter> SKIPS UNIV)\<close>
  by (simp add: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def cfun_eqI)
  
lemma Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Suc2 : \<open>Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Suc i) = (\<Lambda> X. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>((\<sqinter>a\<in>UNIV \<rightarrow> X) \<sqinter> SKIPS UNIV))\<close>
  by (simp add: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def cfun_eqI iterate_Suc2 del: iterate_Suc)

lemma Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>(\<Lambda> X. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>(Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S j\<cdot>X)) = Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (i + j)\<close>
  by (simp add: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def cfun_eqI iterate_iterate)


lemma F_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>\<F> (Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P) =
   {(s @ t, X) |s t X. tF s \<and> length s = i \<and> (t, X) \<in> \<F> P} \<union>
   {(t, X). tF t \<and> length t < i \<and> (\<exists>a. ev a \<notin> X)} \<union>
   {(t, X) |t X. tF t \<and> length t < i \<and> (\<exists>r. \<checkmark>(r) \<notin> X)} \<union>
   {(t @ [\<checkmark>(r)], X) |t r X. tF t \<and> length t < i}\<close>
  by (auto simp add: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def iterate_Mndetprefix_SKIPS_is F_Ndet
      F_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV F_iterate_Mndetprefix_UNIV)

lemma D_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>\<D> (Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P) = {s @ t |s t. tF s \<and> length s = i \<and> t \<in> \<D> P}\<close>
  by (auto simp add: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def iterate_Mndetprefix_SKIPS_is D_Ndet
      D_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV D_iterate_Mndetprefix_UNIV)

lemma T_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>\<T> (Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P) = {s. tF s \<and> length s < i} \<union>
                     {s @ t |s t. tF s \<and> length s = i \<and> t \<in> \<T> P} \<union>
                     {t @ [\<checkmark>(r)] |t r. tF t \<and> length t < i}\<close>
  by (auto simp add: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def iterate_Mndetprefix_SKIPS_is T_Ndet
      T_GlobalNdet_iterate_Mndetprefix_UNIV_then_SKIPS_UNIV T_iterate_Mndetprefix_UNIV)


lemmas Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_projs = F_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S D_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S T_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S




text \<open>We then define an operator that ``extends'' this indefinitely,
allowing \<^term>\<open>P\<close> to be prefixed by an arbitrary but finite number \<open>> 0\<close> of iterations.\<close>

definition GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ::
  \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(DFI\<^sup>\<checkmark> _)\<close> [1000] 999)
  where \<open>DFI\<^sup>\<checkmark> P \<equiv> \<sqinter>i \<in> {0<..}. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P\<close>


text \<open>We give below a variant where we also allow \<^term>\<open>Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 0\<close>.
These two operators ought to be linked together with some lemmas.\<close>

definition GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S' ::
  \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(DFI\<^sup>*\<^sup>\<checkmark> _)\<close> [1000] 999)
  where \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<equiv> \<sqinter>i \<in> UNIV. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P\<close>
  \<comment>\<open>of course, \<^prop>\<open>UNIV = {0 :: nat..}\<close>\<close>



subsection \<open>First Properties of \<^term>\<open>DFI\<^sup>\<checkmark> P\<close> and \<^term>\<open>DFI\<^sup>*\<^sup>\<checkmark> P\<close>\<close>

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_is_Ndet_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>DFI\<^sup>*\<^sup>\<checkmark> P = P \<sqinter> DFI\<^sup>\<checkmark> P\<close>
proof -
  have * : \<open>UNIV = insert (0 :: nat) {0<..}\<close> by fast
  have \<open>DFI\<^sup>*\<^sup>\<checkmark>P = \<sqinter> i\<in>UNIV. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P\<close>
    by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_def)
  also have \<open>\<dots> = Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 0\<cdot>P \<sqinter> (\<sqinter> i\<in>{0<..}. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P)\<close>
    by (simp add: "*" GlobalNdet_distrib_unit)
  also have \<open>Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 0\<cdot>P = P\<close> by simp
  also have \<open>(\<sqinter> i\<in>{0<..}. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P) = DFI\<^sup>\<checkmark> P\<close> by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def)
  finally show \<open>DFI\<^sup>*\<^sup>\<checkmark> P = P \<sqinter> DFI\<^sup>\<checkmark> P\<close> .
qed

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D DFI\<^sup>\<checkmark> P\<close>
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_self : \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (simp_all add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_is_Ndet_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S Ndet_FD_self_left Ndet_FD_self_right)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD : \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S trans_FD)

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_def GlobalNdet_refine_FD UNIV_I)

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S : \<open>0 < i \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def GlobalNdet_refine_FD greaterThan_iff)

corollary Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F :
  \<open>0 < i \<Longrightarrow> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F Q\<close>
  by (meson GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S leFD_imp_leF trans_F)

corollary Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_T_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_T :
  \<open>0 < i \<Longrightarrow> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>T Q\<close>
  by (meson GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S leFD_imp_leF leF_imp_leT trans_T)

corollary Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_D_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_D :
  \<open>0 < i \<Longrightarrow> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>D Q\<close>
  by (meson GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S leFD_imp_leD trans_D)

corollary Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD :
  \<open>0 < i \<Longrightarrow> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  by (meson GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S trans_FD)

corollary Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_DT_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_DT :
  \<open>0 < i \<Longrightarrow> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (simp add: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_D_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_D
      Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_T_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_T trace_divergence_refine_def)


lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_neq_BOT [simp] : \<open>DFI\<^sup>\<checkmark> P \<noteq> \<bottom>\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def D_GlobalNdet BOT_iff_Nil_D Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_projs)

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_is_BOT_iff : \<open>DFI\<^sup>*\<^sup>\<checkmark> P = \<bottom> \<longleftrightarrow> P = \<bottom>\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_def D_GlobalNdet BOT_iff_Nil_D Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_projs)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_BOT [simp] : \<open>DFI\<^sup>*\<^sup>\<checkmark> \<bottom> = \<bottom>\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_is_BOT_iff)



lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_is_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>DFI\<^sup>*\<^sup>\<checkmark> (Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>P) = DFI\<^sup>\<checkmark> P\<close> (is \<open>?lhs = _\<close>)
proof -
  have \<open>?lhs = \<sqinter>i\<in>UNIV. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>(Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>P)\<close>
    by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_def)
  also have \<open>\<dots> = \<sqinter>i\<in>UNIV. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Suc i)\<cdot>P\<close>
    by (auto intro!: mono_GlobalNdet_eq simp add: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Suc2 simp del: Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_Suc)
  also have \<open>\<dots> = \<sqinter> i\<in>{0<..}. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P\<close>
    by (simp add: greaterThan_0 mono_GlobalNdet_eq2)
  also have \<open>\<dots> = DFI\<^sup>\<checkmark>P\<close>
    by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def)
  finally show \<open>?lhs = DFI\<^sup>\<checkmark>P\<close> .
qed


lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S' :
  \<open>DFI\<^sup>\<checkmark> P = Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>(DFI\<^sup>*\<^sup>\<checkmark> P)\<close> (is \<open>_ = ?rhs\<close>)
proof -
  have \<open>DFI\<^sup>\<checkmark> P = \<sqinter>i\<in>UNIV. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (Suc i)\<cdot>P\<close>
    by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def greaterThan_0 mono_GlobalNdet_eq2)
  also have \<open>\<dots> = \<sqinter>i\<in>UNIV. (\<sqinter>a\<in>UNIV \<rightarrow> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P) \<sqinter> SKIPS UNIV\<close> by simp
  also have \<open>\<dots> = (\<sqinter>i\<in>UNIV. \<sqinter>a\<in>UNIV \<rightarrow> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P) \<sqinter> SKIPS UNIV\<close>
    by (simp only: GlobalNdet_Ndet[where A = UNIV and Q = \<open>\<lambda>i. SKIPS UNIV\<close>, simplified])
  also have \<open>\<sqinter>i\<in>UNIV. \<sqinter>a\<in>UNIV \<rightarrow> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P = \<sqinter>a\<in>UNIV \<rightarrow> DFI\<^sup>*\<^sup>\<checkmark> P\<close>
    by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_def Mndetprefix_distrib_GlobalNdet)
  finally show \<open>DFI\<^sup>\<checkmark> P = ?rhs\<close> by simp
qed


lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_unfold : \<open>DFI\<^sup>*\<^sup>\<checkmark> P = P \<sqinter> Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>(DFI\<^sup>*\<^sup>\<checkmark> P)\<close>
  by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_is_Ndet_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S,
      simp only: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S')

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold : \<open>DFI\<^sup>\<checkmark> P = Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>(P \<sqinter> DFI\<^sup>\<checkmark> P)\<close>
  by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S')
    (simp only: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_is_Ndet_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)


lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_idempotent : \<open>DFI\<^sup>*\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P) = DFI\<^sup>*\<^sup>\<checkmark> P\<close>
proof -
  have \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D DFI\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close>
  proof (rule failure_divergence_refineI)
    show \<open>t \<in> \<D> (DFI\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P)) \<Longrightarrow> t \<in> \<D> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close> for t
      by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_def D_GlobalNdet D_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)
        (metis tickFree_append_iff append.assoc)
  next
    show \<open>(t, X) \<in> \<F> (DFI\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P)) \<Longrightarrow> (t, X) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close> for t X
    proof (induct t)
      case Nil thus ?case
        by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_unfold)
          (simp add: F_Ndet Mndetprefix_projs GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S')
    next
      case (Cons e t)
      from Cons.prems consider \<open>(e # t, X) \<in> \<F> (SKIPS UNIV)\<close>
        | a where \<open>e = ev a\<close> \<open>(t, X) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close>
        | a where \<open>e = ev a\<close> \<open>(t, X) \<in> \<F> (DFI\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P))\<close>
        by (subst (asm) GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold) (auto simp add: F_Ndet Mndetprefix_projs)
      thus ?case
      proof cases
        show \<open>(e # t, X) \<in> \<F> (SKIPS UNIV) \<Longrightarrow> (e # t, X) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close>
          by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_unfold) (simp add: F_Ndet)
      next
        fix a assume \<open>e = ev a\<close> \<open>(t, X) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close>
        thus \<open>(e # t, X) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close>
          by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_unfold) (simp add: F_Ndet Mndetprefix_projs)
      next
        fix a assume \<open>e = ev a\<close> \<open>(t, X) \<in> \<F> (DFI\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P))\<close>
        from Cons.hyps this(2) have \<open>(t, X) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close> .
        with \<open>e = ev a\<close> show \<open>(e # t, X) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close>
          by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_unfold) (simp add: F_Ndet Mndetprefix_projs)
      qed
    qed
  qed

  have \<open>DFI\<^sup>*\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P) = DFI\<^sup>*\<^sup>\<checkmark> P \<sqinter>  DFI\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close>
    by (fact GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_is_Ndet_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)
  also have \<open>\<dots> = DFI\<^sup>*\<^sup>\<checkmark> P\<close>
    by (metis FD_iff_eq_Ndet \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D DFI\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P)\<close>)
  finally show \<open>DFI\<^sup>*\<^sup>\<checkmark> (DFI\<^sup>*\<^sup>\<checkmark> P) = DFI\<^sup>*\<^sup>\<checkmark> P\<close> .
qed


lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>DFI\<^sup>\<checkmark> (DFI\<^sup>\<checkmark> P) = Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>(DFI\<^sup>\<checkmark> P)\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'
      GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_is_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_idempotent)




subsection \<open>Proving Deadlock Freedom\<close>

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> if \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F P\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  have \<open>tF t \<Longrightarrow> (t, UNIV) \<notin> \<F> (DFI\<^sup>\<checkmark> P)\<close> for t
  proof (induct t)
    case Nil thus ?case
      by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def F_GlobalNdet F_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)
  next
    case (Cons e t)
    then obtain a where \<open>e = ev a\<close> \<open>tF t\<close> \<open>(t, UNIV) \<notin> \<F> (DFI\<^sup>\<checkmark> P)\<close>
      by (meson is_ev_def tickFree_Cons_iff)
    with \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F P\<close> show \<open>(e # t, UNIV) \<notin> \<F> (DFI\<^sup>\<checkmark> P)\<close>
      by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)
        (auto simp add: F_Ndet F_SKIPS Mndetprefix_projs failure_refine_def)
  qed
  thus \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
    by (meson deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_right failure_refine_def subsetD that)
qed



corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_F_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S leFD_imp_leF)




text \<open>Actually, this is an equivalence\<close>

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_restriction_fix_def :
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R = (\<upsilon> x. (\<sqinter>a \<in> A \<rightarrow> x) \<sqinter> SKIPS R)\<close>
  by (rule restriction_fix_unique[symmetric])
    (simp_all flip: DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold)


lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R\<close> if \<open>A \<noteq> {}\<close> \<open>R \<noteq> {}\<close>
proof (unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_restriction_fix_def, induct rule: restriction_fix_ind)
  show \<open>constructive (\<lambda>x. (\<sqinter>a\<in>A \<rightarrow> x) \<sqinter> SKIPS R)\<close> by simp
next
  show \<open>adm\<^sub>\<down> ((\<sqsubseteq>\<^sub>F\<^sub>D) (DFI\<^sup>\<checkmark> P))\<close> by simp
next
  show \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D DFI\<^sup>\<checkmark> P\<close> by simp
next
  show \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D x \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter>a\<in>A \<rightarrow> x) \<sqinter> SKIPS R\<close> for x
    by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_unfold, auto simp add: SKIPS_FD_SKIPS_iff that
        intro: mono_Ndet_FD[OF trans_FD[OF mono_Mndetprefix_FD Mndetprefix_FD_subset]]
        trans_FD[OF Ndet_FD_self_right])
qed

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S empty_not_UNIV trans_FD)


theorem deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_iff_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD :
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD)




\<comment>\<open>Not used but added just for fun (the proof is very elegant):
  \<^term>\<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV\<close> is the unique fixed point
  of the endofunction @{term [source] \<open>\<lambda>P. DFI\<^sup>\<checkmark> P\<close>}.\<close>


lemma Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_constructive : \<open>0 < i \<Longrightarrow> constructive (\<lambda>P. Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S i\<cdot>P)\<close>
  by (induct i rule: nat_induct_non_zero) simp_all

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_constructive : \<open>constructive (\<lambda>P. DFI\<^sup>\<checkmark> P)\<close>
  unfolding GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def
  by (metis GlobalNdet_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k(2) Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_constructive greaterThan_iff)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  [restriction_shift_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simpset, simp] :
  \<open>non_destructive f \<Longrightarrow> constructive (\<lambda>x. DFI\<^sup>\<checkmark> (f x))\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_constructive)


theorem DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_UNIV_UNIV_is_restriction_fix_of_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S :
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV = (\<upsilon> x :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. DFI\<^sup>\<checkmark> x)\<close>
proof (rule restriction_fix_unique[symmetric])
  show \<open>DFI\<^sup>\<checkmark> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) = DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV\<close>
  proof (unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_restriction_fix_def, induct rule: restriction_fix_ind)
    show \<open>constructive (\<lambda>x. (\<sqinter>a\<in>UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV)\<close> by simp
  next
    show \<open>adm\<^sub>\<down> (\<lambda>x. DFI\<^sup>\<checkmark> x = x)\<close> by simp
  next
    show \<open>DFI\<^sup>\<checkmark> (\<upsilon> x. DFI\<^sup>\<checkmark> x) = (\<upsilon> x. DFI\<^sup>\<checkmark> x)\<close>
      by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_constructive restriction_fix_eq)
  next
    fix x :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume \<open>DFI\<^sup>\<checkmark> x = x\<close>
    have \<open>DFI\<^sup>\<checkmark> ((\<sqinter>a\<in>UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV) = DFI\<^sup>\<checkmark> (Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>x)\<close> by simp
    also have \<open>\<dots> = DFI\<^sup>\<checkmark> (Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>(DFI\<^sup>\<checkmark> x))\<close> by (simp only: \<open>DFI\<^sup>\<checkmark> x = x\<close>)
    also have \<open>\<dots> = DFI\<^sup>\<checkmark> (DFI\<^sup>\<checkmark> (DFI\<^sup>\<checkmark> x))\<close>
      unfolding GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ..
    also have \<open>\<dots> = DFI\<^sup>\<checkmark> (DFI\<^sup>\<checkmark> x)\<close> unfolding \<open>DFI\<^sup>\<checkmark> x = x\<close> ..
    also have \<open>\<dots> = Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>(DFI\<^sup>\<checkmark> x)\<close>
      unfolding GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S ..
    also have \<open>\<dots> = Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S 1\<cdot>x\<close> unfolding \<open>DFI\<^sup>\<checkmark> x = x\<close> ..
    also have \<open>\<dots> = (\<sqinter>a\<in>UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV\<close> by simp
    finally show \<open>DFI\<^sup>\<checkmark> ((\<sqinter>a\<in>UNIV \<rightarrow> x) \<sqinter> SKIPS UNIV) = \<dots>\<close> by simp
  qed
next
  show \<open>constructive GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<close> by simp
qed






lemma df_step_intro:
  \<comment>\<open>this version is not applicable to index/parametrized process\<close>
  assumes P_def: \<open>P = Q\<close> and \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  shows \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  by (metis assms GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)


lemma df_step_param_intro:
  \<comment>\<open>this version \<^emph>\<open>is\<close> not applicable to index/parametrized process\<close>
  assumes P_def: \<open>\<And>x. P x = Q x\<close> and \<open>\<And>st_var. DFI\<^sup>\<checkmark> (\<sqinter>a \<in> UNIV. P a) \<sqsubseteq>\<^sub>F\<^sub>D Q st_var\<close>
  shows \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. P n)\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S
      assms empty_not_UNIV mono_GlobalNdet_FD_const)




subsection \<open>Eat lemmas\<close>

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mndetprefix :
  \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a \<in> A \<rightarrow> Q a\<close> if \<open>A \<noteq> {}\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a\<close>
proof -
  have \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>UNIV \<rightarrow> DFI\<^sup>*\<^sup>\<checkmark> P\<close>
    by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_is_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S' Ndet_FD_self_left)
  also have \<open>\<sqinter>a\<in>UNIV \<rightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a \<in> A \<rightarrow> DFI\<^sup>*\<^sup>\<checkmark> P\<close>
    by (simp add: Mndetprefix_FD_subset that(1))
  also have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a \<in> A \<rightarrow> Q a\<close>
    by (simp add: mono_Mndetprefix_FD that(2))
  finally show \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a \<in> A \<rightarrow> Q a\<close> .
qed

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D \<box>a \<in> A \<rightarrow> Q a\<close>
  by (meson Mndetprefix_FD_Mprefix GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mndetprefix trans_FD)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_write :
  \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>!a \<rightarrow> Q\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix write_def)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_write0 :
  \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> Q\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix write0_def)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_read :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>?a \<in> A \<rightarrow> Q a\<close>
  by (simp add: read_def GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix inv_into_into)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_ndet_write :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>!\<^bold>!a \<in> A \<rightarrow> Q a\<close>
  by (simp add: ndet_write_def GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mndetprefix inv_into_into)



text \<open>We also have the following weaker versions.\<close>

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Mndetprefix :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a \<in> A \<rightarrow> Q a\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mndetprefix
      GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Mprefix :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D \<box>a \<in> A \<rightarrow> Q a\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_write :
  \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>!a \<rightarrow> Q\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Mprefix write_def)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_write0 :
  \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> Q\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Mprefix write0_def)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_read :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>?a \<in> A \<rightarrow> Q a\<close>
  by (simp add: read_def GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Mprefix inv_into_into)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_ndet_write :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>!\<^bold>!a \<in> A \<rightarrow> Q a\<close>
  by (simp add: ndet_write_def GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Mndetprefix inv_into_into)



corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mndetprefix :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a \<in> A \<rightarrow> Q a\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mndetprefix
      GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D \<box>a \<in> A \<rightarrow> Q a\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_write :
  \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>!a \<rightarrow> Q\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix write_def)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_write0 :
  \<open>DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D a \<rightarrow> Q\<close>
  by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix write0_def)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_read :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>?a \<in> A \<rightarrow> Q a\<close>
  by (simp add: read_def GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix inv_into_into)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_ndet_write :
  \<open>A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D Q a) \<Longrightarrow> DFI\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D c\<^bold>!\<^bold>!a \<in> A \<rightarrow> Q a\<close>
  by (simp add: ndet_write_def GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mndetprefix inv_into_into)




lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_GlobalNdet : \<open>a \<in> A \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> (\<sqinter>a \<in> A. P a) \<sqsubseteq>\<^sub>F\<^sub>D P a\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_self trans_FD GlobalNdet_refine_FD)

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_SKIPS : \<open>R \<noteq> {} \<Longrightarrow> DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D SKIPS R\<close>
  by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_unfold, simp)
    (meson Ndet_FD_self_right SKIPS_FD_SKIPS_iff order_trans top_greatest)

corollary GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_SKIP : \<open>DFI\<^sup>*\<^sup>\<checkmark> P \<sqsubseteq>\<^sub>F\<^sub>D SKIP r\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_SKIPS SKIPS_singl_is_SKIP empty_not_insert)





lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Interrupt :
  assumes \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D P\<close> and \<open>Q = a \<rightarrow> Q\<close>
  shows \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D  Q \<triangle> P\<close>
proof (unfold refine_defs, safe)
  show \<open>(t, Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> (t, Y) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close> for t Y
  proof (induct t)
    from \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D  P\<close> show \<open>([], Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> ([], Y) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
      by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_unfold, subst (asm) \<open>Q = a \<rightarrow> Q\<close>)
        (simp add: refine_defs F_Ndet F_Interrupt write0_projs Mndetprefix_projs SKIPS_projs subset_iff,
          metis BOT_iff_Nil_D DiffD2 GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_is_BOT_iff insertI1 is_processT8)
  next
    fix e t Y assume hyp : \<open>(t, Y) \<in> \<F> (Q \<triangle> P) \<Longrightarrow> (t, Y) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
    assume \<open>(e # t, Y) \<in> \<F> (Q \<triangle> P)\<close>
    hence \<open>(e # t, Y) \<in> \<F> ((a \<rightarrow> Q) \<triangle> P)\<close> by (subst (asm) \<open>Q = a \<rightarrow> Q\<close>) simp
    then consider \<open>(e # t, Y) \<in> \<F> P\<close> | \<open>e = ev a\<close> \<open>(t, Y) \<in> \<F> (Q \<triangle> P)\<close>
      by (auto simp add: Interrupt_write0 F_Det F_write0)
    thus \<open>(e # t, Y) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
    proof cases
      assume \<open>(e # t, Y) \<in> \<F> P\<close>
      with \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>(e # t, Y) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
        by (simp add: refine_defs subset_iff)
    next
      assume \<open>e = ev a\<close> \<open>(t, Y) \<in> \<F> (Q \<triangle> P)\<close>
      from this(2)[THEN hyp] have \<open>(t, Y) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close> .
      thus \<open>(e # t, Y) \<in> \<F> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
        by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_unfold) (simp add: \<open>e = ev a\<close> Ndet_projs Mndetprefix_projs)
    qed
  qed
next
  show \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> t \<in> \<D> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close> for t
  proof (induct t)
    from \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>[] \<in> \<D> (Q \<triangle> P) \<Longrightarrow> [] \<in> \<D> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
      by (simp add: refine_defs subset_iff D_Interrupt GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_def D_GlobalNdet D_iterate_Mndetprefix_UNIV)
        (metis Nil_notin_D_Mprefix assms(2) write0_def)
  next
    fix e t assume hyp : \<open>t \<in> \<D> (Q \<triangle> P) \<Longrightarrow> t \<in> \<D> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
    assume \<open>e # t \<in> \<D> (Q \<triangle> P)\<close>
    hence \<open>e # t \<in> \<D> ((a \<rightarrow> Q) \<triangle> P)\<close> by (subst (asm) \<open>Q = a \<rightarrow> Q\<close>) simp
    hence \<open>e # t \<in> \<D> P \<or> t \<in> \<D> (Q \<triangle> P)\<close>
      by (auto simp add: D_Interrupt write0_projs)
    thus \<open>e # t \<in> \<D> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
    proof (elim disjE)
      from \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>e # t \<in> \<D> P \<Longrightarrow> e # t \<in> \<D> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
        by (simp add: refine_defs subset_iff)
    next
      assume \<open>t \<in> \<D> (Q \<triangle> P)\<close>
      from this[THEN hyp] \<open>e # t \<in> \<D> (Q \<triangle> P)\<close>[THEN D_imp_front_tickFree]
      show \<open>e # t \<in> \<D> (DFI\<^sup>*\<^sup>\<checkmark> X)\<close>
        by (subst GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_unfold,
          cases e, simp_all add: Ndet_projs Mndetprefix_projs SKIPS_projs front_tickFree_Cons_iff)
          (metis BOT_iff_Nil_D GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_is_BOT_iff \<open>e # t \<in> \<D> (Q \<triangle> P)\<close> \<open>t \<in> \<D> (Q \<triangle> P)\<close>)
    qed
  qed
qed



lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_GlobalDet_Guard :
  assumes \<open>\<exists>i\<in>I. b i\<close> \<open>\<And>i. i \<in> I \<Longrightarrow> b i \<Longrightarrow> \<sqinter>a \<in> UNIV \<rightarrow> DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D P i\<close>
  shows \<open>DFI\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D \<box> i\<in>I. b i \<^bold>& P i\<close>
proof (rule trans_FD)
  show \<open>DFI\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>UNIV \<rightarrow> DFI\<^sup>*\<^sup>\<checkmark> X\<close>
    by (simp add: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mndetprefix)
next
  show \<open>\<sqinter>a\<in>UNIV \<rightarrow>  DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D \<box>i\<in>I. b i \<^bold>& P i\<close>
    by (simp add: assms mono_GlobalDet_Guard_FD_const)
qed


(*this lemma is not used in the proof method, but used in an example for manual proof, so kept here*)
lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_GlobalDet_Guard :
  assumes \<open>\<exists>i\<in>I. b i\<close> \<open>\<And>i. i \<in> I \<Longrightarrow> b i \<Longrightarrow> \<sqinter>a \<in> UNIV \<rightarrow> DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D P i\<close>
  shows \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D \<box> i\<in>I. b i \<^bold>& P i\<close>
  by (intro GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_GlobalDet_Guard assms)


end