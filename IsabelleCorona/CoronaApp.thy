section \<open>Application example from IoT healthcare\<close> 
text \<open>The  example of an IoT healthcare systems is taken from the context of the CHIST-ERA project
   by (simp add: corona_scenario'_def ex_graph'_def pub_def shop_def atI_def ex_loc_ass_def)
SUCCESS \cite{suc:16}.  In this system architecture, data is collected by sensors 
in the home or via a smart phone helping to monitor bio markers of the patient. The data 
collection is in a cloud based server to enable hospitals (or scientific institutions) 
to access the data which is controlled via the smart phone.
The identities Patient and Doctor represent patients
and their doctors; double quotes ''s'' indicate strings 
in Isabelle/HOL.
The global policy is `only the patient and the doctor can access the data in the cloud'.\<close>
theory CoronaApp
imports Infrastructure
begin
text \<open>Local policies are represented as a function over an @{text \<open>igraph G\<close>} 
      that additionally assigns each location of a scenario to its local policy 
      given as a pair of requirements to an actor (first element of the pair) in 
      order to grant him actions in the location (second element of the pair). 
      The predicate @{text \<open>@G\<close>} checks whether an actor is at a given location 
       in the @{text \<open>igraph G\<close>}.\<close>
locale scenarioCorona = 

fixes corona_actors :: "identity set"
defines corona_actors_def: "corona_actors \<equiv> {''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve''}"

fixes corona_locations :: "location set"
defines corona_locations_def: "corona_locations \<equiv> {Location 0, Location 1}"
fixes pub :: "location"
defines pub_def: "pub \<equiv> Location 0"
fixes shop :: "location"
defines shop_def: "shop \<equiv> Location 1"

fixes identifiable :: "[infrastructure,actor,efid, location] \<Rightarrow> bool"
defines identifiable_def: "identifiable I a eid l\<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> kgra (graphI I) a l \<and> Eid = eid}"
fixes global_policy :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policy_def: "global_policy I eid \<equiv>  (\<exists> l. \<not>(identifiable I (Actor ''Eve'') eid l))"

fixes identifiable' :: "[efid, (identity * efid)set] \<Rightarrow> bool"
defines identifiable'_def: "identifiable' eid A \<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> A \<and> Eid = eid}"

fixes global_policy' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policy'_def: "global_policy' I eid \<equiv>  
             \<not>(identifiable' eid (\<Inter> {A. (\<exists> l \<in> nodes(graphI I). (A = (kgra(graphI I)(Actor ''Eve'') l)))  }))"

fixes ex_creds :: "identity \<Rightarrow> (string set * string set * efid)"
defines ex_creds_def: 
          "ex_creds \<equiv> (\<lambda> x. if x = ''Alice'' then ({}, {}, Efid 1) else 
                            (if x = ''Bob'' then  ({},{}, Efid 2) else 
                            (if x = ''Charly'' then ({},{}, Efid 3) else
                            (if x = ''David'' then ({},{}, Efid 4) else
                            (if x = ''Eve'' then ({},{}, Efid 5) else ({},{},Efid 0))))))"

fixes ex_locs :: "location \<Rightarrow> string * (dlm * data) set"
defines "ex_locs \<equiv> (\<lambda> x. ('''',{}))"

fixes ex_loc_ass :: "location \<Rightarrow> identity set"
defines ex_loc_ass_def: "ex_loc_ass \<equiv>
          (\<lambda> x. if x = pub then {''Alice'', ''Bob'', ''Eve''}  
                 else (if x = shop then {''Charly'', ''David''} 
                       else {}))"
fixes ex_loc_ass' :: "location \<Rightarrow> identity set"
defines ex_loc_ass'_def: "ex_loc_ass' \<equiv>
          (\<lambda> x. if x = pub then {''Alice'', ''Eve''}  
                 else (if x = shop then { ''Bob'', ''Charly'', ''David''} 
                       else {}))"
fixes ex_loc_ass'' :: "location \<Rightarrow> identity set"
defines ex_loc_ass''_def: "ex_loc_ass'' \<equiv>
          (\<lambda> x. if x = pub then {''Alice''}  
                 else (if x = shop then {''Eve'', ''Bob'', ''Charly'', ''David''} 
                       else {}))"

fixes ex_efids :: "location \<Rightarrow> efid set"
defines ex_efids_def: "ex_efids \<equiv> 
          (\<lambda> x. if x = pub then {Efid 1, Efid 2, Efid 5}
                else (if x = shop then {Efid 3, Efid 4}
                      else {}))"

fixes ex_efids' :: "location \<Rightarrow> efid set"
defines ex_efids'_def: "ex_efids' \<equiv> 
          (\<lambda> x. if x = pub then {Efid 1, Efid 5}
                else (if x = shop then {Efid 2, Efid 3, Efid 4}
                      else {}))"

fixes ex_efids'' :: "location \<Rightarrow> efid set"
defines ex_efids''_def: "ex_efids'' \<equiv> 
          (\<lambda> x. if x = pub then {Efid 1}
                else (if x = shop then {Efid 5, Efid 2, Efid 3, Efid 4}
                      else {}))"

fixes ex_knos :: "actor \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knos_def: "ex_knos \<equiv> (\<lambda> x :: actor. 
                  (if x = Actor ''Eve'' then (\<lambda> l :: location. {} :: (identity * efid) set) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knos' :: "actor \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knos'_def: "ex_knos' \<equiv> (\<lambda> x :: actor. 
                  (if x = Actor ''Eve'' then 
                     (\<lambda> l :: location.
                        (if l = pub then 
                                  ({(''Alice'', Efid 1),(''Alice'', Efid 2),(''Alice'', Efid 5),
                                    (''Bob'', Efid 1),(''Bob'', Efid 2),(''Bob'', Efid 5),
                                    (''Eve'', Efid 1),(''Eve'', Efid 2),(''Eve'', Efid 5)})
                         else {})) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knos'' :: "actor \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knos''_def: "ex_knos'' \<equiv> (\<lambda> x :: actor.                       
                  (if x = Actor ''Eve'' then 
                      (\<lambda> l :: location.
                           (if l = pub then 
                                  ({(''Alice'', Efid 1),(''Alice'', Efid 2),(''Alice'', Efid 5),
                                    (''Bob'', Efid 1),(''Bob'', Efid 2),(''Bob'', Efid 5),
                                    (''Eve'', Efid 1),(''Eve'', Efid 2),(''Eve'', Efid 5)})
                            else (if l = shop then 
                                     ({(''Eve'', Efid 5),(''Eve'', Efid 2),(''Eve'', Efid 3),(''Eve'', Efid 4),
                                       (''Bob'', Efid 5),(''Bob'', Efid 2),(''Bob'', Efid 3),(''Bob'', Efid 4), 
                                       (''Charly'', Efid 5),(''Charly'', Efid 2),(''Charly'', Efid 3),(''Charly'', Efid 4),
                                       (''David'', Efid 5),(''David'', Efid 2),(''David'', Efid 3),(''David'', Efid 4)})
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
fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph {(pub, shop)} ex_loc_ass ex_creds ex_locs ex_efids ex_knos"

(* Eve gets the ex_knos *)
fixes ex_graph' :: "igraph"
defines ex_graph'_def: "ex_graph' \<equiv> Lgraph {(pub, shop)} ex_loc_ass ex_creds ex_locs ex_efids ex_knos'"

(* Bob goes to shop *)
fixes ex_graph'' :: "igraph"
defines ex_graph''_def: "ex_graph'' \<equiv> Lgraph {(pub, shop)} ex_loc_ass' ex_creds ex_locs ex_efids' ex_knos'"

(* Eve goes to shop *)
fixes ex_graph''' :: "igraph"
defines ex_graph'''_def: "ex_graph''' \<equiv> Lgraph {(pub, shop)} ex_loc_ass'' ex_creds ex_locs ex_efids'' ex_knos'"

(* Eve gets ex_knos at shop *)
fixes ex_graph'''' :: "igraph"
defines ex_graph''''_def: "ex_graph'''' \<equiv> Lgraph {(pub, shop)} ex_loc_ass'' ex_creds ex_locs ex_efids'' ex_knos''"

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

fixes local_policies :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_def: "local_policies G \<equiv> 
    (\<lambda> x. if x = pub then  {(\<lambda> y. True, {get,move})}
          else (if x = shop then {(\<lambda> y. True, {get,move})} 
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

fixes corona_scenario :: "infrastructure"
defines corona_scenario_def:
"corona_scenario \<equiv> Infrastructure ex_graph local_policies"
fixes Icorona :: "infrastructure set"
defines Icorona_def:
  "Icorona \<equiv> {corona_scenario}"

(* other states of scenario *)
(* First step: Bob goes to shop *)

fixes corona_scenario' :: "infrastructure"
defines corona_scenario'_def: "corona_scenario' \<equiv> Infrastructure ex_graph' local_policies"
fixes Corona' :: "infrastructure set"
defines Corona'_def: "Corona' \<equiv> {corona_scenario'}"
fixes corona_scenario'' :: "infrastructure"
defines corona_scenario''_def: "corona_scenario'' \<equiv> Infrastructure ex_graph'' local_policies"
fixes Corona'' :: "infrastructure set"
defines Corona''_def: "Corona'' \<equiv> {corona_scenario''}"
fixes corona_scenario''' :: "infrastructure"
defines corona_scenario'''_def: "corona_scenario''' \<equiv> Infrastructure ex_graph''' local_policies"
fixes Corona''' :: "infrastructure set"
defines Corona'''_def: "Corona''' \<equiv> {corona_scenario'''}"
fixes corona_scenario'''' :: "infrastructure"
defines corona_scenario''''_def: "corona_scenario'''' \<equiv> Infrastructure ex_graph'''' local_policies"
fixes Corona'''' :: "infrastructure set"
defines Corona''''_def: "Corona'''' \<equiv> {corona_scenario''''}"

fixes corona_states
defines corona_states_def: "corona_states \<equiv> { I. corona_scenario \<rightarrow>\<^sub>i* I }"
fixes corona_Kripke
defines "corona_Kripke \<equiv> Kripke corona_states {corona_scenario}"
fixes scorona 
defines "scorona \<equiv> {x. \<exists> n. \<not> global_policy x (Efid n)}"  

  (*  We assume the Insider assumption for Eve being able to impersonate Charly but
     we only need it in a positive sense to ensure that other actors can be assumed to 
     be unique, that is, that the function Actor is injective on their identities. This 
     is needed only to evaluate the credentials function that ranges over type actor. 

fixes astate:: "identity \<Rightarrow> actor_state"
defines astate_def: "astate x \<equiv>  (case x of 
           ''Eve'' \<Rightarrow> Actor_state depressed {revenge, peer_recognition}
          | _ \<Rightarrow> Actor_state happy {})"
assumes Eve_precipitating_event: "tipping_point (astate ''Eve'')"
assumes Insider_Eve: "Insider ''Eve'' {''Charly''} astate" *)

begin
subsection \<open>Using Attack Tree Calculus\<close>
text \<open>Since we consider a predicate transformer semantics, we use sets of states 
     to represent properties. For example, the attack property is given by the above
     @{text \<open>set scorona\<close>}.

The attack we are interested in is to see whether for the scenario

@{text \<open>corona scenario \<equiv> Infrastructure ex_graph local_policies\<close>}

from the initial state 

@{text \<open>Icorona \<equiv>{corona scenario}\<close>}, 

the critical state
@{text \<open>scorona\<close>} can be reached, i.e., is there a valid attack @{text \<open>(Icorona,scorona)\<close>}?

We first present a number of lemmas showing single and multi-step state transitions
for relevant states reachable from our @{text \<open>corona_scenario\<close>}.\<close>

thm global_policy'_def
lemma bla: "global_policy' I eid \<Longrightarrow> global_policy I eid"
  apply (simp add: global_policy'_def)
  oops
(*
lemma "Actor ''Eve'' = Actor ''Charly''"
  using Eve_precipitating_event Insider_Eve Insider_def UasI_def by blast

lemma Alice_Bob_neq: "Actor ''Bob'' \<noteq> Actor ''Alice''"
  apply (insert Eve_precipitating_event Insider_Eve)
  apply (simp add: Insider_def UasI_def tipping_point_def astate_def)
  apply (subgoal_tac "''Bob'' \<noteq> ''Alice''")
  apply (smt char.inject list.inject)
  by blast

lemma Alice_David_neq: \<open>Actor ''Eve'' \<noteq> Actor ''David''\<close>
  by (smt Eve_precipitating_event Insider_Eve Insider_def UasI_def char.inject list.inject singletonI)

lemma Charly_Bob_neq: \<open>Actor ''Charly'' \<noteq> Actor ''Bob''\<close>
  by (smt Eve_precipitating_event Insider_Eve Insider_def UasI_def char.inject list.inject singletonI)

lemma Charly_Alice_neq: \<open>Actor ''Charly'' \<noteq> Actor ''Alice''\<close>
  by (smt Eve_precipitating_event Insider_Eve Insider_def UasI_def char.inject list.inject singletonI)
*)

lemma step1: "corona_scenario  \<rightarrow>\<^sub>n corona_scenario'"
proof (rule_tac l = pub and a = "''Eve''" and l = pub in get)
  show "graphI corona_scenario = graphI corona_scenario" by (rule refl)
next show "''Eve'' @\<^bsub>graphI corona_scenario\<^esub> pub" 
    by (simp add: corona_scenario_def ex_graph_def ex_loc_ass_def atI_def nodes_def)
next show "enables corona_scenario pub (Actor ''Eve'') get"
    by (simp add: enables_def corona_scenario_def ex_graph_def local_policies_def
                    ex_creds_def ex_locs_def has_def credentials_def)
next show "corona_scenario' =
    Infrastructure
     (Lgraph (gra (graphI corona_scenario)) (agra (graphI corona_scenario)) (cgra (graphI corona_scenario))
       (lgra (graphI corona_scenario)) (egra (graphI corona_scenario))
       ((kgra (graphI corona_scenario))
        (Actor ''Eve'' := (kgra (graphI corona_scenario) (Actor ''Eve''))
           (pub := {(x, y). x \<in> agra (graphI corona_scenario) pub \<and> y \<in> egra (graphI corona_scenario) pub}))))
     (delta corona_scenario)"
    apply (simp add: corona_scenario'_def ex_graph'_def move_graph_a_def 
                     corona_scenario_def ex_graph_def pub_def shop_def 
                     ex_loc_ass'_def ex_loc_ass_def ex_efids'_def ex_efids_def 
                     ex_knos_def ex_knos'_def ex_creds_def)
    apply (rule ext, simp add: insert_Diff_if shop_def efemid_def pub_def)
      apply (rule impI, rule ext)
by auto[1]
qed

lemma step1r: "corona_scenario  \<rightarrow>\<^sub>n* corona_scenario'"
proof (simp add: state_transition_in_refl_def)
  show " (corona_scenario, corona_scenario') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1, auto)
qed


lemma step2: "corona_scenario'  \<rightarrow>\<^sub>n corona_scenario''"
proof (rule_tac l' = shop and l = pub and a = "''Bob''" in move, rule refl)
  show "''Bob'' @\<^bsub>graphI corona_scenario'\<^esub> pub"
   by (simp add: corona_scenario'_def ex_graph'_def pub_def shop_def atI_def ex_loc_ass_def)
next show "pub \<in> nodes (graphI corona_scenario')"
    by (simp add: corona_scenario'_def ex_graph'_def pub_def atI_def nodes_def, blast)
next show "shop \<in> nodes (graphI corona_scenario')"
    by (simp add: corona_scenario'_def nodes_def ex_graph'_def, blast)
next show "''Bob'' \<in> actors_graph (graphI corona_scenario')"
    by (simp add: actors_graph_def corona_scenario'_def ex_graph'_def nodes_def
                     ex_loc_ass_def shop_def pub_def, blast)
next show "enables corona_scenario' shop (Actor ''Bob'') move"
    by (simp add: enables_def corona_scenario'_def local_policies_def)
next show "corona_scenario'' =
    Infrastructure (move_graph_a ''Bob'' pub shop (graphI corona_scenario')) (delta corona_scenario')"
    apply (simp add: corona_scenario'_def ex_graph''_def move_graph_a_def corona_scenario''_def 
                     ex_graph'_def ex_loc_ass_def ex_loc_ass'_def shop_def pub_def)
    apply (rule conjI)
      apply (rule ext, simp add: insert_Diff_if shop_def efemid_def pub_def)
    apply (simp add: ex_efids_def ex_efids'_def shop_def pub_def ex_creds_def)
    by (rule ext, simp add: insert_Diff_if shop_def efemid_def pub_def)
qed

lemma step2r: "corona_scenario'  \<rightarrow>\<^sub>n* corona_scenario''"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenario', corona_scenario'') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2, auto)
qed

lemma step3: "corona_scenario''  \<rightarrow>\<^sub>n corona_scenario'''"
proof (rule_tac l' = shop and l = pub and a = "''Eve''" in move, rule refl)
  show "''Eve'' @\<^bsub>graphI corona_scenario''\<^esub> pub"
   by (simp add: corona_scenario''_def ex_graph''_def pub_def shop_def atI_def ex_loc_ass'_def)
next show \<open>pub \<in> nodes (graphI corona_scenario'')\<close>
    by (simp add: corona_scenario''_def pub_def ex_graph''_def nodes_def, blast)
next show \<open>shop \<in> nodes (graphI corona_scenario'')\<close>
    by (simp add: corona_scenario''_def pub_def ex_graph''_def nodes_def, blast)
next show \<open>''Eve'' \<in> actors_graph (graphI corona_scenario'')\<close>
    by (simp add: actors_graph_def corona_scenario''_def ex_graph''_def nodes_def ex_loc_ass'_def 
                  shop_def pub_def, blast)
next show \<open>enables corona_scenario'' shop (Actor ''Eve'') move\<close>
    by (simp add: enables_def corona_scenario''_def local_policies_def)
next show \<open>corona_scenario''' =
    Infrastructure (move_graph_a ''Eve'' pub shop (graphI corona_scenario'')) (delta corona_scenario'')\<close>
    apply (simp add: corona_scenario'''_def ex_graph'''_def move_graph_a_def pub_def shop_def
                     corona_scenario''_def ex_graph''_def ex_loc_ass''_def ex_loc_ass'_def)
    apply (rule conjI)
     apply (rule ext, simp add: insert_Diff_if shop_def efemid_def pub_def)+
    apply (simp add: ex_efids'_def ex_efids''_def shop_def pub_def ex_creds_def)
    by (simp add: insert_Diff_if shop_def efemid_def pub_def)
qed
   
lemma step3r: "corona_scenario''  \<rightarrow>\<^sub>n* corona_scenario'''"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenario'', corona_scenario''') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step3, auto)
qed

lemma step4: "corona_scenario'''  \<rightarrow>\<^sub>n corona_scenario''''"
proof (rule_tac l = shop and a = "''Eve''" in get, rule refl)
  show \<open>''Eve'' @\<^bsub>graphI corona_scenario'''\<^esub> shop\<close>
   by (simp add: corona_scenario'''_def ex_graph'''_def pub_def shop_def atI_def ex_loc_ass''_def)
next show \<open>enables corona_scenario''' shop (Actor ''Eve'') get\<close>
    by (simp add: enables_def corona_scenario'''_def local_policies_def)
next show \<open>corona_scenario'''' =
    Infrastructure
     (Lgraph (gra (graphI corona_scenario''')) (agra (graphI corona_scenario''')) (cgra (graphI corona_scenario'''))
       (lgra (graphI corona_scenario''')) (egra (graphI corona_scenario'''))
       ((kgra (graphI corona_scenario'''))
        (Actor ''Eve'' := (kgra (graphI corona_scenario''') (Actor ''Eve''))
           (shop := {(x, y). x \<in> agra (graphI corona_scenario''') shop \<and> y \<in> egra (graphI corona_scenario''') shop}))))
     (delta corona_scenario''') \<close>
    apply (simp add: corona_scenario'''_def ex_graph'''_def move_graph_a_def pub_def shop_def
                     corona_scenario''''_def ex_graph''''_def ex_loc_ass''_def ex_loc_ass'_def)
     apply (rule ext, simp add: insert_Diff_if shop_def efemid_def pub_def)+
    apply (simp add: ex_efids''_def shop_def pub_def ex_knos'_def ex_knos''_def)
    apply (rule impI, rule ext)
    apply (simp add: insert_Diff_if shop_def efemid_def pub_def)
    by auto
qed

lemma step4r: "corona_scenario'''  \<rightarrow>\<^sub>n* corona_scenario''''"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenario''', corona_scenario'''') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step4, auto)
qed


text \<open>For the Kripke structure

@{text \<open>corona_Kripke \<equiv> Kripke { I. corona_scenario \<rightarrow>\<^sub>i* I } {corona_scenario}\<close>}

we first derive a valid and-attack using the attack tree proof calculus.

@{text \<open>"\<turnstile>[\<N>\<^bsub>(Icorona,Corona')\<^esub>, \<N>\<^bsub>(Corona',Corona'')\<^esub>, \<N>\<^bsub>(GDPR',scorona)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Icorona,scorona)\<^esup>\<close>}

The set @{text \<open>GDPR'\<close>} (see above) is an intermediate state where Eve accesses the cloud.\<close>

lemma corona_ref: "[\<N>\<^bsub>(Icorona,scorona)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Icorona,scorona)\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(Icorona,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',scorona)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Icorona,scorona)\<^esup>)"  
proof (rule_tac l = "[]" and l' = "[\<N>\<^bsub>(Icorona,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',scorona)\<^esub>]" and
                  l'' = "[]" and si = Icorona and si' = Icorona and 
                  si'' = scorona and si''' = scorona in refI, simp, rule refl)
  show "([\<N>\<^bsub>(Icorona, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', scorona)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Icorona, scorona)\<^esup>) =
    ([] @ [\<N>\<^bsub>(Icorona, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', scorona)\<^esub>] @ [] \<oplus>\<^sub>\<and>\<^bsup>(Icorona, scorona)\<^esup>)"
  by simp
qed

lemma att_corona: "\<turnstile>([\<N>\<^bsub>(Icorona,GDPR')\<^esub>, \<N>\<^bsub>(GDPR',scorona)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Icorona,scorona)\<^esup>)"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(Icorona, GDPR')\<^esub>"
    apply (simp add: Icorona_def GDPR'_def att_base)
    using state_transition_infra_def step1 by blast
next show "\<turnstile>([\<N>\<^bsub>(GDPR', scorona)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(GDPR', scorona)\<^esup>)"
    apply (subst att_and, simp)
    apply (simp add: GDPR'_def scorona_def att_base)
    apply (subst state_transition_infra_def)
    apply (rule_tac x = corona_scenario'' in exI)
    apply (rule conjI)
     apply (simp add: global_policy'_def corona_scenario''_def corona_actors_def 
                      enables_def local_policies_def cloud_def sphone_def)
    by (rule step2)
qed

lemma corona_abs_att: "\<turnstile>\<^sub>V([\<N>\<^bsub>(Icorona,scorona)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Icorona,scorona)\<^esup>)"
  by (rule ref_valI, rule corona_ref, rule att_corona)

text \<open>We can then simply apply the Correctness theorem @{text \<open>AT EF\<close>} to immediately 
      prove the following CTL statement.

      @{text \<open>corona_Kripke \<turnstile> EF scorona\<close>}

This application of the meta-theorem of Correctness of attack trees saves us
proving the CTL formula tediously by exploring the state space.\<close>
lemma corona_att: "corona_Kripke \<turnstile> EF {x. \<not>(global_policy' x ''Eve'')}"
proof -
  have a: " \<turnstile>([\<N>\<^bsub>(Icorona, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', scorona)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Icorona, scorona)\<^esup>)"
    by (rule att_corona)
  hence "(Icorona,scorona) = attack ([\<N>\<^bsub>(Icorona, GDPR')\<^esub>, \<N>\<^bsub>(GDPR', scorona)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(Icorona, scorona)\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>Icorona. i \<rightarrow>\<^sub>i* s} Icorona \<turnstile> EF scorona"
    using ATV_EF corona_abs_att by fastforce 
  thus "corona_Kripke \<turnstile> EF {x::infrastructure. \<not> global_policy' x ''Eve''}"
    by (simp add: corona_Kripke_def corona_states_def Icorona_def scorona_def)
qed

theorem corona_EF: "corona_Kripke \<turnstile> EF scorona"
  using corona_att scorona_def by blast 

text \<open>Similarly, vice-versa, the CTL statement proved in @{text \<open>corona_EF\<close>}
    can now be directly translated into Attack Trees using the Completeness 
    Theorem\footnote{This theorem could easily 
    be proved as a direct instance of @{text \<open>att_corona\<close>} above but we want to illustrate
    an alternative proof method using Completeness here.}.\<close>
theorem corona_AT: "\<exists> A. \<turnstile> A \<and> attack A = (Icorona,scorona)"
  using att_corona attack.simps(2) by blast  
(* old proof that uses Completeness and does not use att_corona:
theorem corona_AT: "\<exists> A. \<turnstile> A \<and> attack A = (Icorona,scorona)"
proof -
  have a: "corona_Kripke \<turnstile> EF scorona " by (rule corona_EF)
  have b: "Icorona \<noteq> {}" by (simp add: Icorona_def)
  thus "\<exists>A::infrastructure attree. \<turnstile>A \<and> attack A = (Icorona, scorona)" 
    apply (rule Completeness)
     apply (simp add: Icorona_def)
    apply (insert a)
    by (simp add: corona_Kripke_def Icorona_def corona_states_def)
qed
*)

text \<open>Conversely, since we have an attack given by rule @{text \<open>corona_AT\<close>}, we can immediately 
   infer @{text \<open>EF s\<close>} using Correctness @{text \<open>AT_EF\<close>}\footnote{Clearly, this theorem is identical
   to @{text \<open>corona_EF\<close>} and could thus be inferred from that one but we want to show here an 
   alternative way of proving it using the Correctness theorem @{text \<open>AT_EF\<close>}.}.\<close>
theorem corona_EF': "corona_Kripke \<turnstile> EF scorona"
  using corona_EF by auto
(* older version of  proof that uses AT_EF and does not use corona_EF:
    by (auto simp: corona_Kripke_def corona_states_def Icorona_def dest: AT_EF) *)

(* However, when integrating DLM into the model and hence labeling
   information becomes part of the conditions of the get_data rule this isn't
   possible any more: corona_EF is not true any more *)    
(** GDPR properties  for the illustration of the DLM labeling **)    
section \<open>Data Protection by Design for GDPR compliance\<close>
subsection \<open>General Data Protection Regulation (GDPR)\<close>
text \<open>Since 26th May 2018, the GDPR has become mandatory within the European Union and hence 
also for any supplier of IT products. Breaches of the regulation will be fined with penalties 
of 20 Million EUR. Despite the relatively large size of the document of 209 pages, the technically 
relevant portion for us is only about 30 pages (Pages 81–111, Chapters I to Chapter III, Section 3). 
In summary, Chapter III specifies that the controller must give the data subject read access (1) 
to any information, communications, and “meta-data” of the data, e.g., retention time and purpose. 
In addition, the system must enable deletion of data (2) and restriction of processing.
An invariant condition for data processing resulting from these Articles is that the system functions 
must preserve any of the access rights of personal data (3).

Using labeled data, we can now express the essence of Article 4 Paragraph (1): 
’personal data’ means any information relating to an identified or identifiable natural 
person (’data subject’).

The labels of data must not be changed by processing: we have identified this  as 
an invariant (3) resulting from the GDPR above. This invariant is formalized in 
our Isabelle model by the type definition of functions on labeled data @{text \<open>label_fun\<close>}
(see Section 4.2) that preserve the data labels.\<close>

subsection \<open>Policy enforcement and privacy preservation\<close>
text \<open>We can now use the labeled data to encode the privacy constraints of the 
    GDPR in the rules. For example, the get data rule (see Section 4.3) has labelled data 
    @{text \<open>((Actor a’, as), n)\<close>} and uses the labeling in the precondition to guarantee 
    that only entitled users can get data.

We can prove that processing preserves ownership as defined in the initial state for all paths 
globally (AG) within the Kripke structure and in all locations of the graph.\<close>
(* GDPR three: Processing preserves ownership in any location *)    
lemma corona_three: "h \<in> corona_actors \<Longrightarrow> l \<in> corona_locations \<Longrightarrow>
         owns (Igraph corona_scenario) l (Actor h) d \<Longrightarrow>
         corona_Kripke \<turnstile> AG {x. \<forall> l \<in> corona_locations. owns (Igraph x) l (Actor h) d }"  
proof (simp add: corona_Kripke_def check_def, rule conjI)
  show "corona_scenario \<in> corona_states" by (simp add: corona_states_def state_transition_refl_def)
next show "h \<in> corona_actors \<Longrightarrow>
    l \<in> corona_locations \<Longrightarrow>
    owns (Igraph corona_scenario) l (Actor h) d \<Longrightarrow>
    corona_scenario \<in> AG {x::infrastructure. \<forall>l::location\<in>corona_locations. owns (Igraph x) l (Actor h) d}"
    apply (simp add: AG_def gfp_def)
    apply (rule_tac x = "{x::infrastructure. \<forall>l::location\<in>corona_locations. owns (Igraph x) l (Actor h) d}" in exI)
    by (auto simp: AX_def corona_scenario_def owns_def)
qed

text \<open>The final application example of Correctness contraposition 
   shows that there is no attack to ownership possible.
The proved meta-theory for attack trees can be applied to facilitate the proof. 
The contraposition of the Correctness property grants that if there is no attack on 
@{text \<open>(I,\<not>f)\<close>}, then @{text \<open>(EF \<not>f)\<close>} does not hold in the Kripke structure. This 
yields the theorem since the @{text \<open>AG f\<close>} statement corresponds to @{text \<open>\<not>(EF \<not>f)\<close>}.
\<close>
theorem no_attack_corona_three: 
"h \<in> corona_actors \<Longrightarrow> l \<in> corona_locations \<Longrightarrow> 
 owns (Igraph corona_scenario) l (Actor h) d \<Longrightarrow>
attack A = (Icorona, -{x. \<forall> l \<in> corona_locations. owns (Igraph x) l (Actor h) d })
\<Longrightarrow> \<not> (\<turnstile> A)"
proof (rule_tac I = Icorona and 
           s = "-{x::infrastructure. \<forall>l::location\<in>corona_locations. owns (Igraph x) l (Actor h) d}" 
       in contrapos_corr)
  show "h \<in> corona_actors \<Longrightarrow>
    l \<in> corona_locations \<Longrightarrow>
    owns (Igraph corona_scenario) l (Actor h) d \<Longrightarrow>
    attack A = (Icorona, - {x::infrastructure. \<forall>l::location\<in>corona_locations. owns (Igraph x) l (Actor h) d}) \<Longrightarrow>
    \<not> (Kripke {s::infrastructure. \<exists>i::infrastructure\<in>Icorona. i \<rightarrow>\<^sub>i* s}
        Icorona \<turnstile> EF (- {x::infrastructure. \<forall>l::location\<in>corona_locations. owns (Igraph x) l (Actor h) d}))"
    apply (rule AG_imp_notnotEF) 
     apply (simp add: corona_Kripke_def Icorona_def corona_states_def)
    apply (drule corona_three, assumption, assumption)
    by (simp add: corona_Kripke_def Icorona_def corona_states_def)
qed
*)
end
end