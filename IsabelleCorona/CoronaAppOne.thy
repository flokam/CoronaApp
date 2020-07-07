theory CoronaAppOne
  imports InfrastructureOne
begin
locale scenarioCoronaOne = scenarioCorona +

  fixes corona_actorsO :: "identity set"
defines corona_actorsO_def: "corona_actorsO \<equiv> {''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve''}"

fixes corona_locationsO :: "location set"
defines corona_locationsO_def: "corona_locationsO \<equiv> {Location 0, Location 1}"
fixes pubO :: "location"
defines pubO_def: "pubO \<equiv> Location 0"
fixes shopO :: "location"
defines shopO_def: "shopO \<equiv> Location 1"

(* not relevant any more. It was made for earlier versions where the intersection happened
   implicitly in the semantics. 
fixes identifiable :: "[infrastructure,actor,efid, location] \<Rightarrow> bool"
defines identifiable_def: "identifiable I a eid l\<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> kgra (graphI I) a l \<and> Eid = eid}"
fixes global_policy :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policy_def: "global_policy I eid \<equiv>  (\<exists> l. \<not>(identifiable I (Actor ''Eve'') eid l))"
*)

fixes identifiableO' :: "[efid, (identity * efid)set] \<Rightarrow> bool"
defines identifiableO'_def: "identifiableO' eid A \<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> A \<and> Eid = eid}"

(* This version is apparently different from the below global_policy'' where we use the image operator
fixes global_policy' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policy'_def: "global_policy' I eid \<equiv>  
             \<not>(identifiable' eid 
                ((\<Inter> {A. (\<exists> l \<in> nodes(graphI I). (A = (kgra(graphI I)(Actor ''Eve'') l)))})
                 - {(x,y). x = ''Eve''}))"
*)

fixes global_policyO'' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policyO''_def: "global_policyO'' I eid \<equiv>  
             \<not>(identifiableO' eid 
                ((\<Inter> (kgra(graphI I)(Actor ''Eve'')`(nodes(graphI I))))
                 - {(x,y). x = ''Eve''}))"

fixes ex_credsO :: "identity \<Rightarrow> (string set * string set * efidlist)"
defines ex_credsO_def: 
          "ex_credsO \<equiv> (\<lambda> x. if x = ''Alice'' then ({}, {}, 
                              Efids (Efid 1) 0 [Efid 11, Efid 21, Efid 31, Efid 41]) else 
                            (if x = ''Bob'' then  ({},{}, 
                              Efids (Efid 2) 0 [Efid 12, Efid 22, Efid 32, Efid 42]) else 
                            (if x = ''Charly'' then ({},{}, 
                              Efids (Efid 3) 0 [Efid 13, Efid 23, Efid 33, Efid 43]) else
                            (if x = ''David'' then ({},{}, 
                              Efids (Efid 4) 0 [Efid 14, Efid 24, Efid 34, Efid 44]) else
                            (if x = ''Eve'' then ({},{}, 
                              Efids (Efid 5) 0 [Efid 15, Efid 25, Efid 35, Efid 35]) else 
                                 ({},{}, Efids (Efid 0) 0 [Efid 10, Efid 20, Efid 30, Efid 40]))))))"

fixes ex_locsO :: "location \<Rightarrow> string * (dlm * data) set"
defines "ex_locsO \<equiv> (\<lambda> x. ('''',{}))"

fixes ex_loc_assO :: "location \<Rightarrow> identity set"
defines ex_loc_assO_def: "ex_loc_assO \<equiv>
          (\<lambda> x. if x = pubO then {''Alice'', ''Bob'', ''Eve''}  
                 else (if x = shopO then {''Charly'', ''David''} 
                       else {}))"
fixes ex_loc_assO' :: "location \<Rightarrow> identity set"
defines ex_loc_assO'_def: "ex_loc_assO' \<equiv>
          (\<lambda> x. if x = pubO then {''Alice'', ''Eve''}  
                 else (if x = shopO then { ''Bob'', ''Charly'', ''David''} 
                       else {}))"
fixes ex_loc_assO'' :: "location \<Rightarrow> identity set"
defines ex_loc_assO''_def: "ex_loc_assO'' \<equiv>
          (\<lambda> x. if x = pubO then {''Alice''}  
                 else (if x = shopO then {''Eve'', ''Bob'', ''Charly'', ''David''} 
                       else {}))"

fixes ex_efidsO :: "location \<Rightarrow> efid set"
defines ex_efidsO_def: "ex_efidsO \<equiv> 
          (\<lambda> x. if x = pubO then {Efid 11, Efid 12, Efid 15}
                else (if x = shopO then {Efid 13, Efid 14}
                      else {}))"

fixes ex_efidsO' :: "location \<Rightarrow> efid set"
defines ex_efidsO'_def: "ex_efidsO' \<equiv> 
          (\<lambda> x. if x = pubO then {Efid 11, Efid 15}
                else (if x = shopO then {Efid 12, Efid 13, Efid 14}
                      else {}))"

fixes ex_efidsO'' :: "location \<Rightarrow> efid set"
defines ex_efidsO''_def: "ex_efidsO'' \<equiv> 
          (\<lambda> x. if x = pubO then {Efid 11}
                else (if x = shopO then {Efid 15, Efid 12, Efid 13, Efid 14}
                      else {}))"

fixes ex_knosO :: "actor \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosO_def: "ex_knosO \<equiv> (\<lambda> x :: actor. 
                  (if x = Actor ''Eve'' then (\<lambda> l :: location. {} :: (identity * efid) set) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knosO' :: "actor \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosO'_def: "ex_knosO' \<equiv> (\<lambda> x :: actor. 
                  (if x = Actor ''Eve'' then 
                     (\<lambda> l :: location.
                        (if l = pubO then 
                                  ({(''Alice'', Efid 11),(''Alice'', Efid 12),(''Alice'', Efid 15),
                                    (''Bob'', Efid 11),(''Bob'', Efid 12),(''Bob'', Efid 15),
                                    (''Eve'', Efid 11),(''Eve'', Efid 12),(''Eve'', Efid 15)})
                         else {})) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knosO'' :: "actor \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosO''_def: "ex_knosO'' \<equiv> (\<lambda> x :: actor.                       
                  (if x = Actor ''Eve'' then 
                      (\<lambda> l :: location.
                           (if l = pubO then 
                                  ({(''Alice'', Efid 11),(''Alice'', Efid 12),(''Alice'', Efid 15),
                                    (''Bob'', Efid 11),(''Bob'', Efid 12),(''Bob'', Efid 15),
                                    (''Eve'', Efid 11),(''Eve'', Efid 12),(''Eve'', Efid 15)})
                            else (if l = shopO then 
                                     ({(''Eve'', Efid 15),(''Eve'', Efid 12),(''Eve'', Efid 13),(''Eve'', Efid 14),
                                       (''Bob'', Efid 15),(''Bob'', Efid 12),(''Bob'', Efid 13),(''Bob'', Efid 14), 
                                       (''Charly'', Efid 15),(''Charly'', Efid 12),(''Charly'', Efid 13),(''Charly'', Efid 14),
                                       (''David'', Efid 15),(''David'', Efid 12),(''David'', Efid 13),(''David'', Efid 14)})
                                   else {})))
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

(* The nicer representation with case suffers from
   not so nice presentation in the cases (need to unfold the syntax)  
fixes ex_loc_ass_alt :: "location \<Rightarrow> identity set"
defines ex_loc_ass_alt_def: "ex_loc_ass_alt \<equiv>
          (\<lambda> x.  (case x of 
             Location (Suc 0) \<Rightarrow> {''Alice'', ''Bob'', ''Eve''}  
           | Location (Suc (Suc 0)) \<Rightarrow> {''Charly'', ''David''} 
           |  _ \<Rightarrow> {}))"
*)

(* initial *)
fixes ex_graphO :: "igraph"
defines ex_graphO_def: "ex_graphO \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO ex_credsO ex_locsO ex_efidsO ex_knosO"

(* Eve gets the ex_knos *)
fixes ex_graphO' :: "igraph"
defines ex_graphO'_def: "ex_graphO' \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO ex_credsO ex_locsO ex_efidsO ex_knosO'"

(* Bob goes to shop *)
fixes ex_graphO'' :: "igraph"
defines ex_graphO''_def: "ex_graphO'' \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO' ex_credsO ex_locsO ex_efidsO' ex_knosO'"

(* Eve goes to shop *)
fixes ex_graphO''' :: "igraph"
defines ex_graphO'''_def: "ex_graphO''' \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO'' ex_credsO ex_locsO ex_efidsO'' ex_knosO'"

(* Eve gets ex_knos at shop *)
fixes ex_graphO'''' :: "igraph"
defines ex_graphO''''_def: "ex_graphO'''' \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO'' ex_credsO ex_locsO ex_efidsO'' ex_knosO''"

(* Same as above: the nicer representation with case suffers from
   not so nice presentation in the cases (need to unfold the syntax) 
fixes local_policies_alt :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_alt_def: "local_policies_alt G \<equiv> 
    (\<lambda> x. case x of 
         Location (Suc 0) \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
       | Location 0 \<Rightarrow> {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
       | Location (Suc (Suc (Suc 0))) \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
       | Location (Suc (Suc 0)) \<Rightarrow>
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} 
       | _ \<Rightarrow>  {})"
*)

fixes local_policiesO :: "[igraph, location] \<Rightarrow> policy set"
defines local_policiesO_def: "local_policiesO G \<equiv> 
    (\<lambda> x. if x = pubO then  {(\<lambda> y. True, {get,move})}
          else (if x = shopO then {(\<lambda> y. True, {get,move})} 
                else {}))"

(* problems with case in locales?
defines local_policies_def: "local_policies G x \<equiv> 
     (case x of 
       home \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
     | sphone \<Rightarrow> {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
     | cloud \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
     | hospital \<Rightarrow> {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} 
     | _ \<Rightarrow>  {})"
*)

fixes rmapO :: "InfrastructureOne.infrastructure \<Rightarrow> Infrastructure.infrastructure"
defines rmapO_def:
"rmapO I \<equiv> InfrastructureOne.ref_map I local_policies"

fixes corona_scenarioO :: "infrastructure"
defines corona_scenarioO_def:
"corona_scenarioO \<equiv> Infrastructure ex_graphO local_policiesO"
fixes IcoronaO :: "infrastructure set"
defines IcoronaO_def:
  "IcoronaO \<equiv> {corona_scenarioO}"

(* other states of scenario *)
(* First step: Bob goes to shop *)

fixes corona_scenarioO' :: "infrastructure"
defines corona_scenarioO'_def: "corona_scenarioO' \<equiv> Infrastructure ex_graphO' local_policiesO"
fixes CoronaO' :: "infrastructure set"
defines CoronaO'_def: "CoronaO' \<equiv> {corona_scenarioO'}"
fixes corona_scenarioO'' :: "infrastructure"
defines corona_scenarioO''_def: "corona_scenarioO'' \<equiv> Infrastructure ex_graphO'' local_policiesO"
fixes CoronaO'' :: "infrastructure set"
defines Corona''_def: "CoronaO'' \<equiv> {corona_scenarioO''}"
fixes corona_scenarioO''' :: "infrastructure"
defines corona_scenarioO'''_def: "corona_scenarioO''' \<equiv> Infrastructure ex_graphO''' local_policiesO"
fixes CoronaO''' :: "infrastructure set"
defines CoronaO'''_def: "CoronaO''' \<equiv> {corona_scenarioO'''}"
fixes corona_scenarioO'''' :: "infrastructure"
defines corona_scenarioO''''_def: "corona_scenarioO'''' \<equiv> Infrastructure ex_graphO'''' local_policiesO"
fixes CoronaO'''' :: "infrastructure set"
defines CoronaO''''_def: "CoronaO'''' \<equiv> {corona_scenarioO''''}"

fixes corona_statesO
defines corona_statesO_def: "corona_statesO \<equiv> { I. corona_scenarioO \<rightarrow>\<^sub>i* I }"
fixes corona_KripkeO
defines "corona_KripkeO \<equiv> Kripke corona_statesO IcoronaO"
fixes scoronaO 
defines "scoronaO \<equiv> {x. \<exists> n. \<not> global_policyO'' x (Efid n)}"  

begin

lemma refmapOne_lem: "\<forall>s::InfrastructureOne.infrastructure.
       (Corona_scenarioO, s) \<in> {(x::InfrastructureOne.infrastructure, y::InfrastructureOne.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>s'::InfrastructureOne.infrastructure. s \<rightarrow>\<^sub>n s' \<longrightarrow> rmapO s \<rightarrow>\<^sub>n rmapO s')"
  oops

theorem refmapOne: "corona_Kripke \<sqsubseteq>\<^sub>rmapO corona_KripkeO"
  oops

lemma step1: "corona_scenarioO  \<rightarrow>\<^sub>n corona_scenarioO'"
  oops

lemma step1r: "corona_scenarioO  \<rightarrow>\<^sub>n* corona_scenarioO'"
  oops

lemma step2: "corona_scenarioO'  \<rightarrow>\<^sub>n corona_scenarioO''"
  oops

lemma step2r: "corona_scenarioO'  \<rightarrow>\<^sub>n* corona_scenarioO''"
  oops

lemma step3: "corona_scenarioO''  \<rightarrow>\<^sub>n corona_scenarioO'''"
  oops

lemma step3r: "corona_scenarioO''  \<rightarrow>\<^sub>n* corona_scenarioO'''"
  oops

lemma step4: "corona_scenarioO'''  \<rightarrow>\<^sub>n corona_scenarioO''''"
  oops

lemma step4r: "corona_scenarioO'''  \<rightarrow>\<^sub>n* corona_scenarioO''''"
  oops

lemma corona_refO: "[\<N>\<^bsub>(IcoronaO,scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO)\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO)\<^esup>)"
  oops

lemma att_coronaO: "\<turnstile>([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO)\<^esup>)"
  oops

lemma corona_abs_attO: "\<turnstile>\<^sub>V([\<N>\<^bsub>(IcoronaO,scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO)\<^esup>)"
  oops

lemma corona_attO: "corona_KripkeO \<turnstile> EF {x. \<exists> n. \<not>(global_policyO'' x (Efid n))}"
  oops

theorem corona_EFO: "corona_KripkeO \<turnstile> EF scoronaO"
  oops

theorem corona_AOO: "\<exists> A. \<turnstile> A \<and> attack A = (IcoronaO,scoronaO)"
  oops

theorem corona_EFO': "corona_KripkeO \<turnstile> EF scoronaO"
  oops

end
end
