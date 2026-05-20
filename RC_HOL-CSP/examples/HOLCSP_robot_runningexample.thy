theory HOLCSP_robot_runningexample 
	imports "RC_HOL-CSP.RoboChart_Library"
begin

subsection \<open> Model \<close>
(*
 This file contains three versions of Trans models:
 - core Trans with inv = ((obs=1 \<or> obs=-1)\<and> (pos \<le>dest)), it is proved as ddlf
 - core Trans with inv = True, a counterexample is found
 - core Trans with no enrichment of a-g, a counterexample is found
*)


thm normalisation
	
datatype NIDS = 
	NID_i0 | 
	NID_detect | 
	NID_stop| 
	NID_move | 
	NID_f0 
instantiation NIDS :: discrete_cpo
begin

definition below_NIDS_def:
  "(x::NIDS) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_def)

end
 
\<comment> \<open>constant and function declaration/definition\<close>
consts dest :: "nat"
	
\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>var_channels_ctrl_robot_ctrl\<close>

"get_obs" "int"  |"set_obs" "int"  |	
\<comment> \<open>internal_stm0channel_stmbd\<close>

"internal_stm0" "NIDS"  |	
\<comment> \<open>flowchannel_stmbd\<close>

"interrupt"  |"exited"  |"exit"  |	
\<comment> \<open>var_channel_stmbd\<close>

"get_pos" "nat"  |"set_pos" "nat"  |"setL_pos" "nat"  |"setR_pos" "nat"  |	
\<comment> \<open>shared_var_channel_stmbd\<close>

"set_EXT_obs" "int"  |	
\<comment> \<open>event_channel_stmbd\<close>

"arrival_in"  |"arrival_out"  |
"arrival__in" "NIDS"  |	
\<comment> \<open>junction_channel_in_stmbd_i0\<close>

"enter_i0"  |"interrupt_i0"  |	
\<comment> \<open>state_channel_in_stmbd_detect\<close>

"enter_detect"  |"entered_detect"  |"interrupt_detect"  |"enteredL_detect"  |"enteredR_detect"  |	
\<comment> \<open>state_channel_in_stmbd_stop\<close>

"enter_stop"  |"entered_stop"  |"interrupt_stop"  |"enteredL_stop"  |"enteredR_stop"  |	
\<comment> \<open>state_channel_in_stmbd_move\<close>

"enter_move"  |"entered_move"  |"interrupt_move"  |"enteredL_move"  |"enteredR_move"  |	
\<comment> \<open>state_channel_in_stmbd_f0\<close>

"enter_f0"  |"entered_f0"  |"interrupt_f0"  |"enteredL_f0"  |"enteredR_f0"  |	
\<comment> \<open>assumption-guarantee_viol\<close>

"aviol"  |"gviol" 	
      
abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"
abbreviation "SSTOP \<equiv> SSTOP_aux share"  


locale controller_proc_robot_ctrl 
begin
fixrec  
Trans :: "NIDS \<rightarrow> chan_event process"  and (*a-g enriched, inv = ((obs=1 \<or> obs=-1)\<and> (pos \<le>dest)), ddlf*)
Trans_ag_true :: "NIDS \<rightarrow> chan_event process"and (*a-g enriched, inv = True, counterexample found*)
Trans_no_ag :: "NIDS \<rightarrow> chan_event process" (*a-g not enriched, same result as the 2nd one: counterexample found, as it is equivalent to the 2nd one*)
where

[simp del]:"Trans\<cdot>n = ((SSTOP \<triangle> (get_obs\<^bold>?obs \<rightarrow> (get_pos\<^bold>?pos \<rightarrow> (assume ((obs=1 \<or> obs = -1 )\<and> (pos \<le>dest)) (Trans\<cdot>n) (((((((((n = NID_i0) \<^bold>& (((internal_stm0\<^bold>.NID_i0 \<rightarrow> Skip)\<^bold>;  (enter_detect \<rightarrow> Trans\<cdot>NID_detect))))
  \<box>
  ((n = NID_detect) \<^bold>& ((((obs = 1)) \<^bold>& (((internal_stm0\<^bold>.NID_detect \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> Skip)\<^bold>;  (enter_stop \<rightarrow> Trans\<cdot>NID_stop))))))))))
  \<box>
  ((n = NID_stop) \<^bold>& (((internal_stm0\<^bold>.NID_stop\<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> Skip)\<^bold>;  (enter_f0 \<rightarrow> Trans\<cdot>NID_f0))))))))
  \<box>
  ((n = NID_move) \<^bold>& ((((pos = dest)) \<^bold>& (((internal_stm0\<^bold>.NID_move \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (arrival_out \<rightarrow> Skip)))\<^bold>;  (enter_stop \<rightarrow> Trans\<cdot>NID_stop))))))))))
  \<box>
  ((n = NID_detect) \<^bold>& ((((obs = (-1))) \<^bold>& (((internal_stm0\<^bold>.NID_detect \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> Skip)\<^bold>;  (enter_move \<rightarrow> Trans\<cdot>NID_move))))))))))
 
\<box>
   ((n = NID_move) \<^bold>& ((((pos < dest)) \<^bold>& (((internal_stm0\<^bold>.NID_move \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (get_pos\<^bold>?pos \<rightarrow> (assume ((obs=1 \<or> obs = -1)\<and> (pos \<le>dest)) (Trans\<cdot>n)  (SSTOP \<triangle> (guar ((obs=1  \<or> obs = -1 )\<and> (pos \<le>dest)) (set_pos\<^bold>!(pos + 1) \<rightarrow> (enter_detect \<rightarrow> Trans\<cdot>NID_detect)))))))) ))))))))
)
  \<box>
  ((n = NID_f0) \<^bold>& (terminate \<rightarrow> Skip)))
 ))   ))))" |

[simp del]:"Trans_ag_true\<cdot>n = ((SSTOP \<triangle> (get_obs\<^bold>?obs \<rightarrow> (get_pos\<^bold>?pos \<rightarrow> (assume True (Trans_ag_true\<cdot>n) (((((((((n = NID_i0) \<^bold>& (((internal_stm0\<^bold>.NID_i0 \<rightarrow> Skip)\<^bold>;  (enter_detect \<rightarrow> Trans_ag_true\<cdot>NID_detect))))
  \<box>
  ((n = NID_detect) \<^bold>& ((((obs = 1)) \<^bold>& (((internal_stm0\<^bold>.NID_detect \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> Skip)\<^bold>;  (enter_stop \<rightarrow> Trans_ag_true\<cdot>NID_stop))))))))))
  \<box>
  ((n = NID_stop) \<^bold>& (((internal_stm0\<^bold>.NID_stop\<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> Skip)\<^bold>;  (enter_f0 \<rightarrow> Trans_ag_true\<cdot>NID_f0))))))))
  \<box>
  ((n = NID_move) \<^bold>& ((((pos = dest)) \<^bold>& (((internal_stm0\<^bold>.NID_move \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (arrival_out \<rightarrow> Skip)))\<^bold>;  (enter_stop \<rightarrow> Trans_ag_true\<cdot>NID_stop))))))))))
  \<box>
  ((n = NID_detect) \<^bold>& ((((obs = (-1))) \<^bold>& (((internal_stm0\<^bold>.NID_detect \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> Skip)\<^bold>;  (enter_move \<rightarrow> Trans_ag_true\<cdot>NID_move))))))))))
 
\<box>
   ((n = NID_move) \<^bold>& ((((pos < dest)) \<^bold>& (((internal_stm0\<^bold>.NID_move \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (get_pos\<^bold>?pos \<rightarrow> (assume (True) (Trans_ag_true\<cdot>n)  (SSTOP \<triangle> (guar (True) (set_pos\<^bold>!(pos + 1) \<rightarrow> (enter_detect \<rightarrow> Trans_ag_true\<cdot>NID_detect)))))))) ))))))))
)
  \<box>
  ((n = NID_f0) \<^bold>& (terminate \<rightarrow> Skip))  )
 ))   ))))" |

[simp del]:"Trans_no_ag\<cdot>n = ((SSTOP \<triangle> (get_obs\<^bold>?obs \<rightarrow> (get_pos\<^bold>?pos \<rightarrow> ( (((((((((n = NID_i0) \<^bold>& (((internal_stm0\<^bold>.NID_i0 \<rightarrow> Skip)\<^bold>;  (enter_detect \<rightarrow> Trans_no_ag\<cdot>NID_detect))))
  \<box>
  ((n = NID_detect) \<^bold>& ((((obs = 1)) \<^bold>& (((internal_stm0\<^bold>.NID_detect \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> Skip)\<^bold>;  (enter_stop \<rightarrow> Trans_no_ag\<cdot>NID_stop))))))))))
  \<box>
  ((n = NID_stop) \<^bold>& (((internal_stm0\<^bold>.NID_stop\<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> Skip)\<^bold>;  (enter_f0 \<rightarrow> Trans_no_ag\<cdot>NID_f0))))))))
  \<box>
  ((n = NID_move) \<^bold>& ((((pos = dest)) \<^bold>& (((internal_stm0\<^bold>.NID_move \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (arrival_out \<rightarrow> Skip)))\<^bold>;  (enter_stop \<rightarrow> Trans_no_ag\<cdot>NID_stop))))))))))
  \<box>
  ((n = NID_detect) \<^bold>& ((((obs = (-1))) \<^bold>& (((internal_stm0\<^bold>.NID_detect \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> Skip)\<^bold>;  (enter_move \<rightarrow> Trans_no_ag\<cdot>NID_move))))))))))
 
\<box>
   ((n = NID_move) \<^bold>& ((((pos < dest)) \<^bold>& (((internal_stm0\<^bold>.NID_move \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited \<rightarrow> (SSTOP \<triangle> (get_pos\<^bold>?pos \<rightarrow> (  (SSTOP \<triangle> ( (set_pos\<^bold>!(pos + 1) \<rightarrow> (enter_detect \<rightarrow> Trans_no_ag\<cdot>NID_detect)))))))) ))))))))
)
  \<box>
  ((n = NID_f0) \<^bold>& (terminate \<rightarrow> Skip)))
 ))   ))))" 
(*
declare bi_extchoice_nguard_norm [normalisation]

declare bi_extchoice_nguard_norm' [normalisation]
*)


declare GlobalDet_Guard [normalisation]

lemma Trans_enriched_ddlf:
  "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. Trans\<cdot>n)"
  apply (deadlock_free' P_def:Trans.simps)
  apply blast+
  done


(*counterexample found for inv=True version*)
lemma Trans_ag_true_findcounterexample:
  "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. Trans_ag_true\<cdot>n)"
  apply (find_counterexample P_def: Trans_ag_true.simps)
  nitpick
(*
Nitpick found a counterexample:
  Skolem constants:
    st_var = NID_detect
    obs = -2 = 3
    pos = 5
*)
  oops


(*counterexample found for non_ag version*)
lemma Trans_no_ag_findcounterexample:
  "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. Trans_no_ag\<cdot>n)"
  apply (find_counterexample P_def: Trans_no_ag.simps)
  nitpick
  oops
  

end

end



 



