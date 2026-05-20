theory HOLCSP_turtlebot_makeplan_ddlf_auto
	imports  "RC_HOL-CSP.RoboChart_Library" HOL.Real 
begin

subsection \<open> Model \<close>


	
	
datatype NIDS_MakePlan_Adaptation_Plan = 
	NID_i0_MakePlan_Adaptation_Plan | 
	NID_CalculateRotations_MakePlan_Adaptation_Plan | 
	NID_PlanEmptyRotation_MakePlan_Adaptation_Plan | 
	NID_PlanPositiveRotation_MakePlan_Adaptation_Plan | 
	NID_PlanNegativeRotation_MakePlan_Adaptation_Plan | 
	NID_PlanFullRotation_MakePlan_Adaptation_Plan | 
	NID_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan | 
	NID_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan | 
	NID_f0_MakePlan_Adaptation_Plan 
instantiation NIDS_MakePlan_Adaptation_Plan :: discrete_cpo
begin

definition below_NIDS_MakePlan_Adaptation_Plan_def:
  "(x::NIDS_MakePlan_Adaptation_Plan) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_MakePlan_Adaptation_Plan_def)

end
 

record SpinCommand =
	angleVelocity :: "real"
	duration :: "real"


record SpinConfig =
	commands :: "(SpinCommand list)"
	period :: "int"

record LidarRange =
	angleIncrement :: "real"
	ranges :: "(real list)"
record BoolLidarMask =
	vals :: "(bool list)"
	baseAngle :: "real"
record ProbLidarMask =
  vals :: "(real list)"
	baseAngle :: "real"


\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_MakePlan_Adaptation_Plan\<close>

"internal__MakePlan_Adaptation_Plan" "NIDS_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>flowchannel_stmbd_MakePlan_Adaptation_Plan\<close>

"interrupt_MakePlan_Adaptation_Plan"  |"exited_MakePlan_Adaptation_Plan"  |"exit_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_MakePlan_Adaptation_Plan\<close>

"enter_i0_MakePlan_Adaptation_Plan"  |"interrupt_i0_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>state_channel_in_stmbd_CalculateRotations_MakePlan_Adaptation_Plan\<close>

"enter_CalculateRotations_MakePlan_Adaptation_Plan"  |"entered_CalculateRotations_MakePlan_Adaptation_Plan"  |"interrupt_CalculateRotations_MakePlan_Adaptation_Plan"  |"enteredL_CalculateRotations_MakePlan_Adaptation_Plan"  |"enteredR_CalculateRotations_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>state_channel_in_stmbd_PlanEmptyRotation_MakePlan_Adaptation_Plan\<close>

"enter_PlanEmptyRotation_MakePlan_Adaptation_Plan"  |"entered_PlanEmptyRotation_MakePlan_Adaptation_Plan"  |"interrupt_PlanEmptyRotation_MakePlan_Adaptation_Plan"  |"enteredL_PlanEmptyRotation_MakePlan_Adaptation_Plan"  |"enteredR_PlanEmptyRotation_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>state_channel_in_stmbd_PlanPositiveRotation_MakePlan_Adaptation_Plan\<close>

"enter_PlanPositiveRotation_MakePlan_Adaptation_Plan"  |"entered_PlanPositiveRotation_MakePlan_Adaptation_Plan"  |"interrupt_PlanPositiveRotation_MakePlan_Adaptation_Plan"  |"enteredL_PlanPositiveRotation_MakePlan_Adaptation_Plan"  |"enteredR_PlanPositiveRotation_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>state_channel_in_stmbd_PlanNegativeRotation_MakePlan_Adaptation_Plan\<close>

"enter_PlanNegativeRotation_MakePlan_Adaptation_Plan"  |"entered_PlanNegativeRotation_MakePlan_Adaptation_Plan"  |"interrupt_PlanNegativeRotation_MakePlan_Adaptation_Plan"  |"enteredL_PlanNegativeRotation_MakePlan_Adaptation_Plan"  |"enteredR_PlanNegativeRotation_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>state_channel_in_stmbd_PlanFullRotation_MakePlan_Adaptation_Plan\<close>

"enter_PlanFullRotation_MakePlan_Adaptation_Plan"  |"entered_PlanFullRotation_MakePlan_Adaptation_Plan"  |"interrupt_PlanFullRotation_MakePlan_Adaptation_Plan"  |"enteredL_PlanFullRotation_MakePlan_Adaptation_Plan"  |"enteredR_PlanFullRotation_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>state_channel_in_stmbd_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan\<close>

"enter_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan"  |"entered_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan"  |"interrupt_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan"  |"enteredL_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan"  |"enteredR_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>state_channel_in_stmbd_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan\<close>

"enter_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan"  |"entered_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan"  |"interrupt_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan"  |"enteredL_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan"  |"enteredR_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>state_channel_in_stmbd_f0_MakePlan_Adaptation_Plan\<close>

"enter_f0_MakePlan_Adaptation_Plan"  |"entered_f0_MakePlan_Adaptation_Plan"  |"interrupt_f0_MakePlan_Adaptation_Plan"  |"enteredL_f0_MakePlan_Adaptation_Plan"  |"enteredR_f0_MakePlan_Adaptation_Plan"  |	
\<comment> \<open>assumption-guarantee_viol_MakePlan_Adaptation_Plan\<close>

"aviol"  |"gviol" 	

| 
"get_minMaxRotation"  "real \<times> real " 


abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"
abbreviation "SSTOP \<equiv> SSTOP_aux share" 
 
locale Trans 
begin
fixrec  
Trans_MakePlan_Adaptation_Plan :: "NIDS_MakePlan_Adaptation_Plan \<rightarrow> chan_event process"
where
[simp del] :\<open>Trans_MakePlan_Adaptation_Plan\<cdot>n = 
	((SSTOP \<triangle> (get_minMaxRotation\<^bold>?minMaxRotation \<rightarrow> (assume (fst minMaxRotation \<le> snd minMaxRotation ) (Trans_MakePlan_Adaptation_Plan\<cdot>n) ((((((((((((((((n = NID_i0_MakePlan_Adaptation_Plan) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_i0_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_CalculateRotations_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_CalculateRotations_MakePlan_Adaptation_Plan))))
	  \<box>
	  ((n = NID_CalculateRotations_MakePlan_Adaptation_Plan) \<^bold>& (((((fst minMaxRotation) = (snd minMaxRotation))) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_CalculateRotations_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_PlanEmptyRotation_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_PlanEmptyRotation_MakePlan_Adaptation_Plan))))))))))


	  \<box>
	  ((n = NID_CalculateRotations_MakePlan_Adaptation_Plan) \<^bold>& ((((((fst minMaxRotation) \<ge> 0) \<and> ((fst minMaxRotation) <(snd minMaxRotation)))) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_CalculateRotations_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_PlanPositiveRotation_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_PlanPositiveRotation_MakePlan_Adaptation_Plan))))))))))


	  \<box>
	  ((n = NID_CalculateRotations_MakePlan_Adaptation_Plan) \<^bold>& ((((((fst minMaxRotation) < (snd minMaxRotation)) \<and> ((snd minMaxRotation) \<le> 0))) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_CalculateRotations_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_PlanNegativeRotation_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_PlanNegativeRotation_MakePlan_Adaptation_Plan))))))))))


	  \<box>
	  ((n = NID_CalculateRotations_MakePlan_Adaptation_Plan) \<^bold>& (((((((fst minMaxRotation) < 0) \<and> ((snd minMaxRotation) > 0)) \<and> (((snd minMaxRotation) - (fst minMaxRotation)) > 1))) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_CalculateRotations_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_PlanFullRotation_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_PlanFullRotation_MakePlan_Adaptation_Plan))))))))))



	  \<box>
	  ((n = NID_CalculateRotations_MakePlan_Adaptation_Plan) \<^bold>& (((((((fst minMaxRotation) < 0) \<and> ((snd minMaxRotation) > 0)) \<and> ((snd minMaxRotation) - (fst minMaxRotation) \<le>1)  \<and> ((-(fst minMaxRotation)) \<le> (snd minMaxRotation)))) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_CalculateRotations_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan))))))))))


	  \<box>
	  ((n = NID_CalculateRotations_MakePlan_Adaptation_Plan) \<^bold>& (((((((fst minMaxRotation) < 0) \<and> ((snd minMaxRotation) > 0)) \<and> ((snd minMaxRotation) - (fst minMaxRotation) \<le>1) \<and> ((-(fst minMaxRotation)) > (snd minMaxRotation)))) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_CalculateRotations_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan))))))))))
	  \<box>
	  ((n = NID_PlanEmptyRotation_MakePlan_Adaptation_Plan) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_PlanEmptyRotation_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_f0_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_f0_MakePlan_Adaptation_Plan))))))))
	  \<box>
	  ((n = NID_PlanPositiveRotation_MakePlan_Adaptation_Plan) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_PlanPositiveRotation_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_f0_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_f0_MakePlan_Adaptation_Plan))))))))
	  \<box>
	  ((n = NID_PlanNegativeRotation_MakePlan_Adaptation_Plan) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_PlanNegativeRotation_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_f0_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_f0_MakePlan_Adaptation_Plan))))))))
	  \<box>
	  ((n = NID_PlanFullRotation_MakePlan_Adaptation_Plan) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_PlanFullRotation_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_f0_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_f0_MakePlan_Adaptation_Plan))))))))
	  \<box>
	  ((n = NID_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_PlanPositiveFirstRotation_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_f0_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_f0_MakePlan_Adaptation_Plan))))))))
	  \<box>
	  ((n = NID_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan) \<^bold>& (((internal__MakePlan_Adaptation_Plan\<^bold>.NID_PlanNegativeFirstRotation_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_MakePlan_Adaptation_Plan \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_MakePlan_Adaptation_Plan \<rightarrow> Skip)\<^bold>;  (enter_f0_MakePlan_Adaptation_Plan \<rightarrow> Trans_MakePlan_Adaptation_Plan\<cdot>NID_f0_MakePlan_Adaptation_Plan)))))))
    \<box>
    ( (n = NID_f0_MakePlan_Adaptation_Plan) \<^bold>& (terminate \<rightarrow> Skip))

)
	    )
	   ))))) \<close>



lemma Trans_MakePlan_Adaptation_Plan_core_ddlf:
  "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. Trans_MakePlan_Adaptation_Plan\<cdot>n)  "
  apply (deadlock_free' P_def: Trans_MakePlan_Adaptation_Plan.simps)
  apply (smt (verit, best) Suc_le_mono Zero_not_Suc atLeastAtMost_iff linorder_not_less zero_le)
  done


end
end



