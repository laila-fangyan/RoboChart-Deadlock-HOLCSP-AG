\<comment>\<open> ******************************************************************** 
 * This file contains some results that are specific to RoboChart. 
 ******************************************************************************\<close>

theory RoboChart_Library
imports Proof_Methods
begin

section\<open>RoboChart auxiliary process and Lemmas\<close>

subsection\<open>SSTOP\<close>

definition SSTOP_aux :: \<open>'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>SSTOP_aux evt \<equiv> \<mu> X. evt \<rightarrow> X\<close>

lemma SSTOP_aux_is_DF : \<open>SSTOP_aux evt = DF {evt}\<close>
  unfolding SSTOP_aux_def DF_def Mndetprefix_singl by simp

(* lemma below used as assumptions in non_terminating_Interrupt_Seq*)
lemma non_terminating_SSTOP_aux [normalisation]: \<open>non_terminating (SSTOP_aux evt)\<close>
  by (metis AfterExt.lifelock_free_iff_CHAOS_events_of_leF CHAOS_F_DF
      SSTOP_aux_is_DF events_of_DF lifelock_free_is_non_terminating)

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_SSTOP_aux_Interrupt[reduction]:
  \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D SSTOP_aux evt \<triangle> P\<close> if \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
proof (rule GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Interrupt)
  from \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D P\<close> show \<open>DFI\<^sup>*\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D  P\<close> .
next
  show \<open>SSTOP_aux evt = evt \<rightarrow> SSTOP_aux evt\<close>
    by (auto intro: cont_process_rec[OF SSTOP_aux_def[THEN meta_eq_to_obj_eq]])
qed

lemma GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_SSTOP_aux_Interrupt[reduction]:
  assumes \<open>DFI\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  shows \<open>DFI\<^sup>\<checkmark> X \<sqsubseteq>\<^sub>F\<^sub>D SSTOP_aux evt \<triangle> P\<close>
  by (metis GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_Iter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_1_is_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_SSTOP_aux_Interrupt assms)



method find_counterexample uses P_def =
  (rule df_step_param_intro[OF P_def],
   auto intro!: GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_SSTOP_aux_Interrupt GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_read
                GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_read inj_onI
      simp add: Guard_Guard_is_Guard_conj,
   simp add:  Guard_Det_Guard_to_GlobalDet  GlobalDet_Guard_Det_Guard_to_GlobalDet,
   auto intro!: reduction
  )



end