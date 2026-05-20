\<comment>\<open> ******************************************************************** 
 * This file contains lemmas for the behaviour of external choice with guard,
   especially normalisation results.
 ******************************************************************************\<close>

theory External_Choice_And_Guard
  imports Guard
begin



section \<open>Normalisation Results\<close>

text \<open>In this theory, we establish additional lemmas of
normalisation of \<^const>\<open>Guard\<close> and external choice.
We aim to obtain a global external choice on the right-hand side.\<close>



text \<open>This version rewrites a binary external choice between two guarded processes
as a global deterministic choice (again, of guarded processes).\<close>

lemma Guard_Det_Guard_to_GlobalDet :
  \<open>b \<^bold>& P \<box> c \<^bold>& Q = \<box>i\<in>{0 :: nat..1}. (if i = 0 then b else c) \<^bold>& (if i = 0 then P else Q)\<close>
  by (simp add: atLeast0_atMost_Suc GlobalDet_distrib_unit_bis Det_commute)

text \<open>We then need a second result that we can use one the first
external choice has been normalised: something transforming patterns like
@{term [eta_contract = false]\<open>(\<box> i\<in>{0..n::nat}. b i \<^bold>& P i) \<box> c \<^bold>& Q\<close>}
into a global external choice of guarded processes.
\<close>

lemma GlobalDet_Guard_Det_Guard_to_GlobalDet:
  \<open>(\<box>i\<in>{0..n}. b i \<^bold>& P i) \<box> c \<^bold>& Q =
   \<box>i\<in>{0..Suc n}. (if i \<le> n then b i else c) \<^bold>& (if i \<le> n then P i else Q)\<close>
  (is \<open>?lhs = ?rhs\<close>)
  by (subst Det_commute)
    (auto simp add: atLeast0_atMost_Suc GlobalDet_distrib_unit_bis
      intro!: arg_cong2[where f = \<open>(\<box>)\<close>] mono_GlobalDet_eq)



text \<open>We also provide variants for allowing no \<^const>\<open>Guard\<close> on left-hand side or right-hand side
(immediate consequences through @{thm [source] Guard_True}).\<close>

corollary Det_Guard_to_GlobalDet :
  \<open>P \<box> c \<^bold>& Q = \<box>i\<in>{0..Suc 0}. (if i = 0 then True else c) \<^bold>& (if i = 0 then P else Q)\<close>
  by (fact Guard_Det_Guard_to_GlobalDet[where b = True, simplified])

corollary Guard_Det_to_GlobalDet :
  \<open>b \<^bold>& P \<box> Q = \<box>i\<in>{0..Suc 0}. (if i = 0 then b else True) \<^bold>& (if i = 0 then P else Q)\<close>
  by (fact Guard_Det_Guard_to_GlobalDet[where c = True, simplified])

corollary GlobalDet_Guard_Det_to_GlobalDet :
  \<open>(\<box>i\<in>{0..n}. b i \<^bold>& P i) \<box> Q =
   \<box>i\<in>{0..Suc n}. (if i \<le> n then b i else True) \<^bold>& (if i \<le> n then P i else Q)\<close>
  by (fact GlobalDet_Guard_Det_Guard_to_GlobalDet[where c = True, simplified])



text \<open>Finally, guards can be removed in a global external choice
by filtering the set on which the choice is indexed.\<close>

lemma GlobalDet_Guard : \<open>\<box>i \<in> I. b i \<^bold>& P i = \<box>i \<in> {i \<in> I. b i}. P i\<close>
proof -
  have \<open>I = {i \<in> I. b i} \<union> {i \<in> I. \<not> b i}\<close> by blast
  hence \<open>\<box> i\<in>I. b i \<^bold>& P i = (\<box>i \<in> {i \<in> I. b i}. b i \<^bold>& P i) \<box> (\<box>i \<in> {i \<in> I. \<not> b i}. b i \<^bold>& P i)\<close>
    by (simp add: GlobalDet_factorization_union)
  also have \<open>\<box>i \<in> {i \<in> I. b i}. b i \<^bold>& P i = \<box>i \<in> {i \<in> I. b i}. P i\<close>
    by (auto intro: mono_GlobalDet_eq)
  also have \<open>\<box>i \<in> {i \<in> I. \<not> b i}. b i \<^bold>& P i = \<box>i \<in> {i \<in> I. \<not> b i}. STOP\<close>
    by (auto intro: mono_GlobalDet_eq)
  also have \<open>\<dots> = STOP\<close> by (metis GlobalDet_empty GlobalDet_id)
  finally show \<open>\<box>i \<in> I. b i \<^bold>& P i = \<box>i \<in> {i \<in> I. b i}. P i\<close> by simp
qed



section \<open>Reduction Result\<close>

lemma mono_GlobalDet_Guard_FD_const :
  assumes \<open>\<exists>i\<in>I. b i\<close> \<open>\<And>i. i \<in> I \<Longrightarrow> b i \<Longrightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D P i\<close>
  shows \<open>X \<sqsubseteq>\<^sub>F\<^sub>D \<box>i\<in>I. b i \<^bold>& P i\<close>
proof (unfold GlobalDet_Guard)
  show \<open>X \<sqsubseteq>\<^sub>F\<^sub>D \<box>i \<in> {i \<in> I. b i}. P i\<close>
    by (metis (mono_tags, lifting) GlobalNdet_FD_GlobalDet assms
        empty_iff mem_Collect_eq mono_GlobalNdet_FD_const trans_FD)
qed



end