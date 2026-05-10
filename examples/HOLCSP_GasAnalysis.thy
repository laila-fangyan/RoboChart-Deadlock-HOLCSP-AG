
theory HOLCSP_GasAnalysis
	imports  "RC_HOL-CSP.RoboChart_Library"
begin

subsection \<open> Model \<close>

type_synonym Chem = nat
type_synonym Intensity = nat

datatype Status = 
	noGas | 
	gasD 
instantiation Status :: discrete_cpo
begin

definition below_Status_def:
  "(x::Status) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_Status_def)

end

	
datatype Angle = 
	Left | 
	Right | 
	Back | 
	Front 
instantiation Angle :: discrete_cpo
begin

definition below_Angle_def:
  "(x::Angle) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_Angle_def)

end
 
	
	
datatype NIDS_GasAnalysis_stm_Chemical = 
	NID_i1_GasAnalysis_stm_Chemical | 
	NID_GasDetected_GasAnalysis_stm_Chemical | 
	NID_j1_GasAnalysis_stm_Chemical | 
	NID_Reading_GasAnalysis_stm_Chemical | 
	NID_Analysis_GasAnalysis_stm_Chemical | 
	NID_NoGas_GasAnalysis_stm_Chemical 
instantiation NIDS_GasAnalysis_stm_Chemical :: discrete_cpo
begin

definition below_NIDS_GasAnalysis_stm_Chemical_def:
  "(x::NIDS_GasAnalysis_stm_Chemical) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_GasAnalysis_stm_Chemical_def)

end
 


record GasSensor =
	c :: "Chem"
	i :: "Intensity"

\<comment> \<open>constant and function declaration/definition\<close>
consts location :: "(GasSensor list) \<Rightarrow> Angle"
	
consts goreq :: "Intensity\<times>Intensity \<Rightarrow> bool"
	
consts intensity :: "(GasSensor list) \<Rightarrow> Intensity"
	
consts angle :: "nat \<Rightarrow> Angle"
	
consts analysis :: "(GasSensor list) \<Rightarrow> Status"
	
consts thr :: "Intensity"
	

\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_GasAnalysis_stm_Chemical\<close>

"internal__GasAnalysis_stm_Chemical" "NIDS_GasAnalysis_stm_Chemical"  |	
\<comment> \<open>flowchannel_stmbd_GasAnalysis_stm_Chemical\<close>

"interrupt_GasAnalysis_stm_Chemical"  |"exited_GasAnalysis_stm_Chemical"  |"exit_GasAnalysis_stm_Chemical"  |	
\<comment> \<open>var_channel_stmbd_GasAnalysis_stm_Chemical\<close>

"get_sts" "Status"  |"set_sts" "Status"  |"setL_sts" "Status"  |"setR_sts" "Status"  |
"get_gs" "(GasSensor list)"  |"set_gs" "(GasSensor list)"  |"setL_gs" "(GasSensor list)"  |"setR_gs" "(GasSensor list)"  |
"get_ins" "Intensity"  |"set_ins" "Intensity"  |"setL_ins" "Intensity"  |"setR_ins" "Intensity"  |
"get_anl" "Angle"  |"set_anl" "Angle"  |"setL_anl" "Angle"  |"setR_anl" "Angle"  |	
\<comment> \<open>event_channel_stmbd_GasAnalysis_stm_Chemical\<close>

"gas_in" "(GasSensor list)"  |"gas_out" "(GasSensor list)"  |
"resume_in"  |"resume_out"  |
"turn_in" "Angle"  |"turn_out" "Angle"  |
"stop_in"  |"stop_out"  |
"gas__in" "NIDS_GasAnalysis_stm_Chemical\<times>(GasSensor list)"  |
"gas__in_NID_Reading_GasAnalysis_stm_Chemical" "GasSensor list" |
"resume__in" "NIDS_GasAnalysis_stm_Chemical"  |
"turn__in" "NIDS_GasAnalysis_stm_Chemical\<times>Angle"  |
"stop__in" "NIDS_GasAnalysis_stm_Chemical"  |	
\<comment> \<open>junction_channel_in_stmbd_i1_GasAnalysis_stm_Chemical\<close>

"enter_i1_GasAnalysis_stm_Chemical"  |"interrupt_i1_GasAnalysis_stm_Chemical"  |	
\<comment> \<open>state_channel_in_stmbd_GasDetected_GasAnalysis_stm_Chemical\<close>

"enter_GasDetected_GasAnalysis_stm_Chemical"  |"entered_GasDetected_GasAnalysis_stm_Chemical"  |"interrupt_GasDetected_GasAnalysis_stm_Chemical"  |"enteredL_GasDetected_GasAnalysis_stm_Chemical"  |"enteredR_GasDetected_GasAnalysis_stm_Chemical"  |	
\<comment> \<open>state_channel_in_stmbd_j1_GasAnalysis_stm_Chemical\<close>

"enter_j1_GasAnalysis_stm_Chemical"  |"entered_j1_GasAnalysis_stm_Chemical"  |"interrupt_j1_GasAnalysis_stm_Chemical"  |"enteredL_j1_GasAnalysis_stm_Chemical"  |"enteredR_j1_GasAnalysis_stm_Chemical"  |	
\<comment> \<open>state_channel_in_stmbd_Reading_GasAnalysis_stm_Chemical\<close>

"enter_Reading_GasAnalysis_stm_Chemical"  |"entered_Reading_GasAnalysis_stm_Chemical"  |"interrupt_Reading_GasAnalysis_stm_Chemical"  |"enteredL_Reading_GasAnalysis_stm_Chemical"  |"enteredR_Reading_GasAnalysis_stm_Chemical"  |	
\<comment> \<open>state_channel_in_stmbd_Analysis_GasAnalysis_stm_Chemical\<close>

"enter_Analysis_GasAnalysis_stm_Chemical"  |"entered_Analysis_GasAnalysis_stm_Chemical"  |"interrupt_Analysis_GasAnalysis_stm_Chemical"  |"enteredL_Analysis_GasAnalysis_stm_Chemical"  |"enteredR_Analysis_GasAnalysis_stm_Chemical"  |	
\<comment> \<open>state_channel_in_stmbd_NoGas_GasAnalysis_stm_Chemical\<close>

"enter_NoGas_GasAnalysis_stm_Chemical"  |"entered_NoGas_GasAnalysis_stm_Chemical"  |"interrupt_NoGas_GasAnalysis_stm_Chemical"  |"enteredL_NoGas_GasAnalysis_stm_Chemical"  |"enteredR_NoGas_GasAnalysis_stm_Chemical"  |	
\<comment> \<open>assumption-guarantee_viol_GasAnalysis_stm_Chemical\<close>

"aviol"  |"gviol" 	
      
abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"
abbreviation "SSTOP \<equiv> SSTOP_aux share"  
(*
 * This version has precondition of functions, therefore we set inv = function.precond
 * inv is set for some branches, others are default as True, e.g., line 152 where the vars are sts and ins, they have no inv constraints.
 * Variables in Trans are handled at two places:
    - var in t.cond (Rule 53: vguards)
    - var in actions (Rule 54: StatementInContext)
 * For a fully automated a-g enrichementw, we need to first normalise the branches that need a-g by pushnig all the sequetial composition into the scope after the assume, so that assume inv can cover the behaviour after the assume to the end of that transition branch.
 * But this is now a manual step. 
 * For Rule 55 semantics of a transition's trigger, if it is an input type, we have trigger.src?x, but HOL-CSP does not support this syntax yet, so a workaround is trigger_src?x (e.g., line 154) 
 * TBC: DO WE NEED a-g for an input type transition's trigger ? yes
*)

locale Trans 
begin
fixrec  
Trans_GasAnalysis_stm_Chemical :: "NIDS_GasAnalysis_stm_Chemical \<rightarrow> chan_event process"
where
[simp del] :\<open>Trans_GasAnalysis_stm_Chemical\<cdot>n = 

	((SSTOP \<triangle> (get_sts\<^bold>?sts\<rightarrow> (get_ins\<^bold>?ins \<rightarrow> (assume True (Trans_GasAnalysis_stm_Chemical\<cdot>n) (((((((((
(n = NID_i1_GasAnalysis_stm_Chemical) \<^bold>& (((internal__GasAnalysis_stm_Chemical\<^bold>.NID_i1_GasAnalysis_stm_Chemical \<rightarrow> ((SSTOP \<triangle> (guar True (set_gs\<^bold>![\<lparr>c=0,i=0\<rparr>] \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (guar True (set_anl\<^bold>!Front \<rightarrow> Skip)))))\<^bold>;  (enter_Reading_GasAnalysis_stm_Chemical \<rightarrow> Trans_GasAnalysis_stm_Chemical\<cdot>NID_Reading_GasAnalysis_stm_Chemical))))

  \<box>
	  ((n = NID_Reading_GasAnalysis_stm_Chemical) \<^bold>& ((gas__in_NID_Reading_GasAnalysis_stm_Chemical\<^bold>? gs \<rightarrow>(assume (size(gs) > 0) (Trans_GasAnalysis_stm_Chemical\<cdot>n) (
    (SSTOP \<triangle>(guar (size(gs) > 0)  (set_gs\<^bold>!gs \<rightarrow> Skip)))\<^bold>; 
     SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip)\<^bold>;  
    SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> Skip)\<^bold>;  (enter_Analysis_GasAnalysis_stm_Chemical \<rightarrow> Trans_GasAnalysis_stm_Chemical\<cdot>NID_Analysis_GasAnalysis_stm_Chemical)))
))))
 )
	  \<box>
	  ((n = NID_NoGas_GasAnalysis_stm_Chemical) \<^bold>& (((internal__GasAnalysis_stm_Chemical\<^bold>.NID_NoGas_GasAnalysis_stm_Chemical \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> Skip)\<^bold>;  (enter_Reading_GasAnalysis_stm_Chemical \<rightarrow> Trans_GasAnalysis_stm_Chemical\<cdot>NID_Reading_GasAnalysis_stm_Chemical))))))))
	  \<box>
	  ((n = NID_Analysis_GasAnalysis_stm_Chemical) \<^bold>& ((((sts = noGas)) \<^bold>& (((internal__GasAnalysis_stm_Chemical\<^bold>.NID_Analysis_GasAnalysis_stm_Chemical \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> (SSTOP \<triangle> (resume_out \<rightarrow> Skip)))\<^bold>;  (enter_NoGas_GasAnalysis_stm_Chemical \<rightarrow> Trans_GasAnalysis_stm_Chemical\<cdot>NID_NoGas_GasAnalysis_stm_Chemical))))))))))
	  \<box>
	  ((n = NID_Analysis_GasAnalysis_stm_Chemical) \<^bold>& ((((sts = gasD)) \<^bold>& (((internal__GasAnalysis_stm_Chemical\<^bold>.NID_Analysis_GasAnalysis_stm_Chemical \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> Skip)\<^bold>;  (enter_GasDetected_GasAnalysis_stm_Chemical \<rightarrow> Trans_GasAnalysis_stm_Chemical\<cdot>NID_GasDetected_GasAnalysis_stm_Chemical))))))))))
	  \<box>
	  ((n = NID_GasDetected_GasAnalysis_stm_Chemical) \<^bold>& (((goreq((ins,thr))) \<^bold>& (((internal__GasAnalysis_stm_Chemical\<^bold>.NID_GasDetected_GasAnalysis_stm_Chemical \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> (SSTOP \<triangle> (stop_out \<rightarrow> Skip)))\<^bold>;  (enter_j1_GasAnalysis_stm_Chemical \<rightarrow> Trans_GasAnalysis_stm_Chemical\<cdot>NID_j1_GasAnalysis_stm_Chemical))))))))))
	  \<box>
	  (n = NID_GasDetected_GasAnalysis_stm_Chemical) \<^bold>& 
      (
        (\<not>goreq(ins,thr)) \<^bold>& (
          internal__GasAnalysis_stm_Chemical\<^bold>.NID_GasDetected_GasAnalysis_stm_Chemical \<rightarrow> Skip\<^bold>;
          SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip)\<^bold>;
          (SSTOP \<triangle> (
                      exited_GasAnalysis_stm_Chemical \<rightarrow>  

                        (SSTOP \<triangle> (get_gs\<^bold>?gs \<rightarrow>(assume  (size(gs) > 0) (Trans_GasAnalysis_stm_Chemical\<cdot>n)
                                        ( ((size(gs) > 0) \<^bold>& (SSTOP \<triangle> (guar (size(gs) > 0) (set_anl\<^bold>!location(gs) \<rightarrow> Skip))) \<^bold>; SSTOP \<triangle> (get_anl\<^bold>?anl \<rightarrow> (assume True  (Trans_GasAnalysis_stm_Chemical\<cdot>n) (SSTOP \<triangle> (guar True (turn_out\<^bold>!anl \<rightarrow> Skip))))))   \<^bold>;
                                          (enter_Reading_GasAnalysis_stm_Chemical \<rightarrow> Trans_GasAnalysis_stm_Chemical\<cdot>NID_Reading_GasAnalysis_stm_Chemical)))))
                  ))
      ))
 \<box> 
  (n = NID_j1_GasAnalysis_stm_Chemical) \<^bold>& (terminate \<rightarrow> Skip)
)
	  )
	   )))))) \<close>


lemma Trans_stm4_core_ddlf_auto:
  "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. Trans_GasAnalysis_stm_Chemical\<cdot>n)  "
  apply (deadlock_free' P_def: Trans_GasAnalysis_stm_Chemical.simps)
  using atMost_atLeast0 lessThan_Suc lessThan_Suc_atMost apply force
  using Status.exhaust atLeast0AtMost by auto

end
end



