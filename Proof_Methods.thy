\<comment>\<open> ******************************************************************** 
 * In this file, we configure the automation.
 ******************************************************************************\<close>


theory Proof_Methods 
	imports Inductive_Deadlock_Freedom 
begin


named_theorems proc_def
  and reduction
  and normalisation

declare read_Seq [normalisation]
  and write0_Seq [normalisation]
  and  write_Seq [normalisation] 

declare non_terminating_Interrupt_Seq[normalisation] 
  and non_terminating_Interrupt_Seq_write0[normalisation] 
  and non_terminating_Interrupt_Seq_read[normalisation]

declare  GlobalDet_is_STOP_iff[normalisation]
  and Guard_Det_Guard_to_GlobalDet [normalisation]
  and GlobalDet_Guard_Det_Guard_to_GlobalDet [normalisation]
  and Guard_Guard_is_Guard_conj[normalisation]

declare no_initial_tick_write0[normalisation]
  and no_initial_tick_write[normalisation]
  and no_initial_tick_ndet_write[normalisation]
  and no_initial_tick_read[normalisation]

text\<open>from Reduction\<close>
declare mono_Det_FD_same_lhs[reduction]
  and mono_GlobalDet_FD_const [reduction]
  and mono_GlobalDet_Guard_FD_const [reduction]

text\<open>from Inductive_Deadlock_Freedom\<close>
declare GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mndetprefix[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_Mprefix[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_write[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_write0[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_read[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_ndet_write[reduction]

declare GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Mndetprefix[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_Mprefix[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_write[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_write0[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_read[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_imp_GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_ndet_write[reduction]

declare GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_SKIP[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S'_FD_GlobalNdet[reduction]
  and GNdetIter\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_GlobalDet_Guard[reduction] 




method deadlock_free' uses P_def =
  rule df_step_param_intro[OF P_def],
  rename_tac st_var, case_tac st_var,
  simp_all,
  auto intro!: reduction inj_onI simp add: normalisation




end
