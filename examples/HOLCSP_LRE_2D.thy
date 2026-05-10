
theory HOLCSP_LRE_2D 
	imports  "RC_HOL-CSP.RoboChart_Library" HOL.Real
begin

subsection \<open> Model \<close>


	
	
datatype NIDS_LRE_Beh = 
	NID_OCM_LRE_Beh | 
	NID_MOM_LRE_Beh | 
	NID_HCM_LRE_Beh | 
	NID_CAM_LRE_Beh | 
	NID_i0_LRE_Beh 
instantiation NIDS_LRE_Beh :: discrete_cpo
begin

definition below_NIDS_LRE_Beh_def:
  "(x::NIDS_LRE_Beh) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_LRE_Beh_def)

end
 



\<comment> \<open>constant and function declaration/definition\<close>
consts inOPEZ :: "real\<times>real \<Rightarrow> bool"
	
consts setVel :: "real\<times>real\<times>real \<Rightarrow> real\<times>real"
	
consts dist :: "(real\<times>real)\<times>((real\<times>real) list) \<Rightarrow> real"
	
consts maneuv :: "real\<times>real \<Rightarrow> real\<times>real"
	
consts CDA :: "(real\<times>real)\<times>((real\<times>real) list)\<times>(real\<times>real) \<Rightarrow> real"
	
consts StaticObsDist :: "real"
	
consts HCMVel :: "real"
	
consts MOMVel :: "real"
	
consts MinSafeDist :: "real"
	
consts Obsts :: "((real\<times>real) list)"
	

\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_LRE_Beh\<close>

"internal__LRE_Beh" "NIDS_LRE_Beh"  |	
\<comment> \<open>flowchannel_stmbd_LRE_Beh\<close>

"interrupt_LRE_Beh"  |"exited_LRE_Beh"  |"exit_LRE_Beh"  |	
\<comment> \<open>var_channel_stmbd_LRE_Beh\<close>

"get_pos" "real\<times>real"  |"set_pos" "real\<times>real"  |"setL_pos" "real\<times>real"  |"setR_pos" "real\<times>real"  |
"get_vel" "real\<times>real"  |"set_vel" "real\<times>real"  |"setL_vel" "real\<times>real"  |"setR_vel" "real\<times>real"  |
"get_reqV" "real\<times>real"  |"set_reqV" "real\<times>real"  |"setL_reqV" "real\<times>real"  |"setR_reqV" "real\<times>real"  |	
\<comment> \<open>event_channel_stmbd_LRE_Beh\<close>

"endTask_in"  |"endTask_out"  |
"reqOCM_in"  |"reqOCM_out"  |
"reqMOM_in"  |"reqMOM_out"  |
"reqHCM_in"  |"reqHCM_out"  |
"reqVel_in" "real\<times>real"  |"reqVel_out" "real\<times>real"  |
"advVel_in" "real\<times>real"  |"advVel_out" "real\<times>real"  |
"endTask__in" "NIDS_LRE_Beh"  |
"reqOCM__in" "NIDS_LRE_Beh"  |
"reqMOM__in" "NIDS_LRE_Beh"  |
"reqHCM__in" "NIDS_LRE_Beh"  |
"reqVel__in" "NIDS_LRE_Beh\<times>real\<times>real"  |
"advVel__in" "NIDS_LRE_Beh\<times>real\<times>real"  |	

"reqVel__in_NID_OCM_LRE_Beh" "real\<times>real"|
\<comment> \<open>state_channel_in_stmbd_OCM_LRE_Beh\<close>

"enter_OCM_LRE_Beh"  |"entered_OCM_LRE_Beh"  |"interrupt_OCM_LRE_Beh"  |"enteredL_OCM_LRE_Beh"  |"enteredR_OCM_LRE_Beh"  |	
\<comment> \<open>state_channel_in_stmbd_MOM_LRE_Beh\<close>

"enter_MOM_LRE_Beh"  |"entered_MOM_LRE_Beh"  |"interrupt_MOM_LRE_Beh"  |"enteredL_MOM_LRE_Beh"  |"enteredR_MOM_LRE_Beh"  |	
\<comment> \<open>state_channel_in_stmbd_HCM_LRE_Beh\<close>

"enter_HCM_LRE_Beh"  |"entered_HCM_LRE_Beh"  |"interrupt_HCM_LRE_Beh"  |"enteredL_HCM_LRE_Beh"  |"enteredR_HCM_LRE_Beh"  |	
\<comment> \<open>state_channel_in_stmbd_CAM_LRE_Beh\<close>

"enter_CAM_LRE_Beh"  |"entered_CAM_LRE_Beh"  |"interrupt_CAM_LRE_Beh"  |"enteredL_CAM_LRE_Beh"  |"enteredR_CAM_LRE_Beh"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_LRE_Beh\<close>

"enter_i0_LRE_Beh"  |"interrupt_i0_LRE_Beh"  |	
\<comment> \<open>assumption-guarantee_viol_LRE_Beh\<close>

"aviol"  |"gviol" 	
      
abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"
abbreviation "SSTOP \<equiv> SSTOP_aux share"  

          


 
locale Trans 
begin
fixrec
Trans_LRE_Beh :: "NIDS_LRE_Beh \<rightarrow> chan_event process" and

Trans_LRE_Beh_core :: "NIDS_LRE_Beh \<rightarrow> chan_event process"
where
[simp del] :\<open>Trans_LRE_Beh\<cdot>n = 
	((SSTOP \<triangle> (get_pos\<^bold>?pos \<rightarrow> (get_vel\<^bold>?vel \<rightarrow> (assume True (Trans_LRE_Beh\<cdot>n) (((((((((((((((((((((n = NID_i0_LRE_Beh) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_i0_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_OCM_LRE_Beh))))
	  \<box>
	  ((n = NID_OCM_LRE_Beh) \<^bold>& (((((((((fst vel) * (fst vel)) + ((snd vel) * (snd vel))) \<le> (3 * 3)) \<and> (dist((pos,Obsts)) > 10)) \<and> (\<not>inOPEZ((pos))))) \<^bold>& (((reqMOM__in\<^bold>.NID_OCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_MOM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_MOM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& (((reqOCM__in\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& (((reqOCM__in\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& ((((((((((fst vel) * (fst vel)) + ((snd vel) * (snd vel))) > (3 * 3)) \<and> (dist((pos,Obsts)) \<le> StaticObsDist)) \<and> (CDA((pos,Obsts,vel)) > MinSafeDist)) \<and> (\<not>inOPEZ((pos))))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_HCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_HCM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& ((((inOPEZ((pos)) \<and> ((CDA((pos,Obsts,vel)) > MinSafeDist) \<or> (dist((pos,Obsts)) > StaticObsDist)))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_OCM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& ((((inOPEZ((pos)) \<and> ((CDA((pos,Obsts,vel)) > MinSafeDist) \<or> (dist((pos,Obsts)) > StaticObsDist)))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_OCM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& (((((dist((pos,Obsts)) > StaticObsDist) \<and> (\<not>inOPEZ((pos))))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_MOM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_MOM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_OCM_LRE_Beh) \<^bold>& (((reqVel__in_NID_OCM_LRE_Beh\<^bold>?reqV \<rightarrow> (SSTOP \<triangle> (set_reqV\<^bold>!reqV \<rightarrow> Skip)))\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> ((SSTOP \<triangle> (get_reqV\<^bold>?reqV \<rightarrow> (assume True ((SSTOP \<triangle> (advVel_out\<^bold>!reqV \<rightarrow> Skip))) (SSTOP \<triangle> (advVel_out\<^bold>!reqV \<rightarrow> Skip)))))\<^bold>;  (SSTOP \<triangle> (get_reqV\<^bold>?reqV \<rightarrow> (assume True ((SSTOP \<triangle> (guar True (set_vel\<^bold>!reqV \<rightarrow> Skip)))) (SSTOP \<triangle> (guar True (set_vel\<^bold>!reqV \<rightarrow> Skip))))))))\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& (((endTask__in\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> (SSTOP \<triangle> (advVel_out\<^bold>!(0,0) \<rightarrow> Skip)))\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& (((((CDA((pos,Obsts,vel)) \<le> MinSafeDist) \<and> (dist((pos,Obsts)) \<le> StaticObsDist))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& (((((CDA((pos,Obsts,vel)) \<le> MinSafeDist) \<and> (dist((pos,Obsts)) \<le> StaticObsDist))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_CAM_LRE_Beh) \<^bold>& ((((CDA((pos,Obsts,vel)) > MinSafeDist)) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_CAM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> (SSTOP \<triangle> (advVel_out\<^bold>!(0,0) \<rightarrow> Skip)))\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_OCM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_CAM_LRE_Beh) \<^bold>& (((reqOCM__in\<^bold>.NID_CAM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_CAM_LRE_Beh) \<^bold>& (((((CDA((pos,Obsts,vel)) \<le> MinSafeDist) \<and> (dist((pos,Obsts)) \<le> StaticObsDist))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_CAM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& (((((((((fst pos) + (fst vel)) < 0) \<or> (((fst pos) + (fst vel)) > 99)) \<or> (((snd pos) + (snd vel)) < 0)) \<or> (((snd pos) + (snd vel)) > 99))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& (((((((((fst pos) + (fst vel)) < 0) \<or> (((fst pos) + (fst vel)) > 99)) \<or> (((snd pos) + (snd vel)) < 0)) \<or> (((snd pos) + (snd vel)) > 99))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_CAM_LRE_Beh) \<^bold>& (((((((((fst pos) + (fst vel)) < 0) \<or> (((fst pos) + (fst vel)) > 99)) \<or> (((snd pos) + (snd vel)) < 0)) \<or> (((snd pos) + (snd vel)) > 99))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_CAM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  (share \<rightarrow> Trans_LRE_Beh\<cdot>n))
	  \<box>
	  (((interrupt_LRE_Beh \<rightarrow> (SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_LRE_Beh \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))))))) \<close>
|
[simp del] :\<open>Trans_LRE_Beh_core\<cdot>n = 
	((SSTOP \<triangle> (get_pos\<^bold>?pos \<rightarrow> (get_vel\<^bold>?vel \<rightarrow> (assume True (Trans_LRE_Beh_core\<cdot>n) (((((((((((((((((((((n = NID_i0_LRE_Beh) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_i0_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_OCM_LRE_Beh))))
	  \<box>
	  ((n = NID_OCM_LRE_Beh) \<^bold>& (((((((((fst vel) * (fst vel)) + ((snd vel) * (snd vel))) \<le> (3 * 3)) \<and> (dist((pos,Obsts)) > 10)) \<and> (\<not>inOPEZ((pos))))) \<^bold>& (((reqMOM__in\<^bold>.NID_OCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_MOM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_MOM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& (((reqOCM__in\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& (((reqOCM__in\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& ((((((((((fst vel) * (fst vel)) + ((snd vel) * (snd vel))) > (3 * 3)) \<and> (dist((pos,Obsts)) \<le> StaticObsDist)) \<and> (CDA((pos,Obsts,vel)) > MinSafeDist)) \<and> (\<not>inOPEZ((pos))))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_HCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_HCM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& ((((inOPEZ((pos)) \<and> ((CDA((pos,Obsts,vel)) > MinSafeDist) \<or> (dist((pos,Obsts)) > StaticObsDist)))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_OCM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& ((((inOPEZ((pos)) \<and> ((CDA((pos,Obsts,vel)) > MinSafeDist) \<or> (dist((pos,Obsts)) > StaticObsDist)))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_OCM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& (((((dist((pos,Obsts)) > StaticObsDist) \<and> (\<not>inOPEZ((pos))))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_MOM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_MOM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_OCM_LRE_Beh) \<^bold>& (((reqVel__in_NID_OCM_LRE_Beh\<^bold>?reqV \<rightarrow> (SSTOP \<triangle> (set_reqV\<^bold>!reqV \<rightarrow> Skip)))\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> ((SSTOP \<triangle> (get_reqV\<^bold>?reqV \<rightarrow> (assume True ((SSTOP \<triangle> (advVel_out\<^bold>!reqV \<rightarrow> Skip))) (SSTOP \<triangle> (advVel_out\<^bold>!reqV \<rightarrow> Skip)))))\<^bold>;  (SSTOP \<triangle> (get_reqV\<^bold>?reqV \<rightarrow> (assume True ((SSTOP \<triangle> (guar True (set_vel\<^bold>!reqV \<rightarrow> Skip)))) (SSTOP \<triangle> (guar True (set_vel\<^bold>!reqV \<rightarrow> Skip))))))))\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& (((endTask__in\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> (SSTOP \<triangle> (advVel_out\<^bold>!(0,0) \<rightarrow> Skip)))\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& (((((CDA((pos,Obsts,vel)) \<le> MinSafeDist) \<and> (dist((pos,Obsts)) \<le> StaticObsDist))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& (((((CDA((pos,Obsts,vel)) \<le> MinSafeDist) \<and> (dist((pos,Obsts)) \<le> StaticObsDist))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_CAM_LRE_Beh) \<^bold>& ((((CDA((pos,Obsts,vel)) > MinSafeDist)) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_CAM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> (SSTOP \<triangle> (advVel_out\<^bold>!(0,0) \<rightarrow> Skip)))\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_OCM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_CAM_LRE_Beh) \<^bold>& (((reqOCM__in\<^bold>.NID_CAM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_OCM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_OCM_LRE_Beh))))))))
	  \<box>
	  ((n = NID_CAM_LRE_Beh) \<^bold>& (((((CDA((pos,Obsts,vel)) \<le> MinSafeDist) \<and> (dist((pos,Obsts)) \<le> StaticObsDist))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_CAM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_MOM_LRE_Beh) \<^bold>& (((((((((fst pos) + (fst vel)) < 0) \<or> (((fst pos) + (fst vel)) > 99)) \<or> (((snd pos) + (snd vel)) < 0)) \<or> (((snd pos) + (snd vel)) > 99))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_MOM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_HCM_LRE_Beh) \<^bold>& (((((((((fst pos) + (fst vel)) < 0) \<or> (((fst pos) + (fst vel)) > 99)) \<or> (((snd pos) + (snd vel)) < 0)) \<or> (((snd pos) + (snd vel)) > 99))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_HCM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_CAM_LRE_Beh))))))))))
	  \<box>
	  ((n = NID_CAM_LRE_Beh) \<^bold>& (((((((((fst pos) + (fst vel)) < 0) \<or> (((fst pos) + (fst vel)) > 99)) \<or> (((snd pos) + (snd vel)) < 0)) \<or> (((snd pos) + (snd vel)) > 99))) \<^bold>& (((internal__LRE_Beh\<^bold>.NID_CAM_LRE_Beh \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_LRE_Beh \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_LRE_Beh \<rightarrow> Skip)\<^bold>;  (enter_CAM_LRE_Beh \<rightarrow> Trans_LRE_Beh_core\<cdot>NID_CAM_LRE_Beh))))))))))
	   )
	   )))))) \<close>


declare Det_Guard_to_GlobalDet [normalisation]
  and   Guard_Det_to_GlobalDet [normalisation]



lemma Trans_ddlf:
  "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<sqinter> n \<in> UNIV. Trans_LRE_Beh_core\<cdot>n)  "
  apply (deadlock_free' P_def: Trans_LRE_Beh_core.simps)
  using atLeastAtMost_iff apply blast+
  done




end


end


