theory InfrastructureThree
  imports CoronaAppTwo
begin

text \<open>This is the new element for refining the Ephemeral Id -- simply a list
     of ephemeral ids. The cryptographic details can be added here if needed
     but at the current stage of abstraction we are satisfied with t a list.
   The idea is that the current pointer is the first element and that
   the Efids are popped off once used.\<close>
(* datatype efidlist = Efids "efid" "nat" "efid list" *)

primrec efids_root :: "efidlist \<Rightarrow> efid"
  where "efids_root (Efids e n el) = e"
primrec efids_index :: "efidlist \<Rightarrow> nat"
  where "efids_index (Efids e n el) = n"
primrec efids_inc_ind :: "efidlist \<Rightarrow> efidlist"
  where "efids_inc_ind (Efids e n el) = (Efids e (Suc n) el) "
primrec efids_cur:: "efidlist \<Rightarrow> efid"
  where "efids_cur (Efids e n ef) = ef n"
primrec efids_list :: "efidlist \<Rightarrow> nat \<Rightarrow> efid"
  where "efids_list (Efids e n ef) = ef"
definition repl_efr :: "efidlist \<Rightarrow> efid"
  where "repl_efr el \<equiv> efids_root el" 

datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity set"
                           "identity \<Rightarrow> efidlist"  
                           "location \<Rightarrow> string * (dlm * data) set"
                           "location \<Rightarrow> efid set"
                           "identity \<Rightarrow> location \<Rightarrow> (identity * efid)set"

datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph, location] \<Rightarrow> policy set" 
                       
primrec loc :: "location \<Rightarrow> nat"
where  "loc(Location n) = n"
primrec gra :: "igraph \<Rightarrow> (location * location)set"
where  "gra(Lgraph g a c l e k) = g"
primrec agra :: "igraph \<Rightarrow> (location \<Rightarrow> identity set)"
where  "agra(Lgraph g a c l e k) = a"
primrec cgra :: "igraph \<Rightarrow> identity \<Rightarrow> efidlist"
where  "cgra(Lgraph g a c l e k) = c"
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> string * (dlm * data) set)"
  where  "lgra(Lgraph g a c l e k) = l"
primrec egra :: "igraph \<Rightarrow> location \<Rightarrow> efid set"
  where  "egra(Lgraph g a c l e k) = e"
primrec kgra:: "[igraph, identity, location] \<Rightarrow> (identity * efid)set"
  where "kgra(Lgraph g a c l e k) = k"

definition nodes :: "igraph \<Rightarrow> location set" 
where "nodes g == { x. (? y. ((x,y): gra g) | ((y,x): gra g))}"

definition actors_graph :: "igraph \<Rightarrow> identity set"  
where  "actors_graph g == {x. ? y. y : nodes g \<and> x \<in> (agra g y)}"

primrec graphI :: "infrastructure \<Rightarrow> igraph"
where "graphI (Infrastructure g d) = g"
primrec delta :: "[infrastructure, igraph, location] \<Rightarrow> policy set"
where "delta (Infrastructure g d) = d"
primrec tspace :: "[infrastructure, identity ] \<Rightarrow> efidlist"
  where "tspace (Infrastructure g d) = cgra g"
primrec lspace :: "[infrastructure, location ] \<Rightarrow> string * (dlm * data)set"
  where "lspace (Infrastructure g d) = lgra g"


text \<open>Predicates and projections for the labels to encode their meaning.\<close>
definition owner :: "dlm * data \<Rightarrow> actor" where "owner d \<equiv> fst(fst d)"
definition owns :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"
  where "owns G l a d \<equiv> owner d = a"
definition readers :: "dlm * data \<Rightarrow> actor set"
  where "readers d \<equiv> snd (fst d)"

text \<open>The predicate @{text \<open>has_access\<close>} is true for owners or readers.\<close> 
definition has_access :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"    
where "has_access G l a d \<equiv> owns G l a d \<or> a \<in> readers d"

typedef label_fun = "{f :: dlm * data \<Rightarrow> dlm * data. 
                        \<forall> x:: dlm * data. fst x = fst (f x)}"  
  by (fastforce)

definition secure_process :: "label_fun \<Rightarrow> dlm * data \<Rightarrow> dlm * data" (infixr "\<Updown>" 50)
  where "f  \<Updown> d \<equiv> (Rep_label_fun f) d" 

definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"

definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"

definition behaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "behaviour I \<equiv> {(t,a,a'). enables I t a a'}"

definition misbehaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "misbehaviour I \<equiv> -(behaviour I)"

primrec jonce :: "['a, 'a list] \<Rightarrow> bool"
where
jonce_nil: "jonce a [] = False" |
jonce_cons: "jonce a (x#ls) = (if x = a then (a \<notin> (set ls)) else jonce a ls)"

definition move_graph_a :: "[identity, location, location, igraph] \<Rightarrow> igraph"
where "move_graph_a n l l' g \<equiv> Lgraph (gra g) 
                    (if n \<in> ((agra g) l) \<and>  n \<notin> ((agra g) l') 
                        \<and> card (agra g l') \<ge> 3 \<and> card (agra g l) \<ge> 4 then 
                     ((agra g)(l := (agra g l) - {n}))(l' := (insert n (agra g l')))
                     else (agra g))
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l')  
                        \<and> card (agra g l') \<ge> 3 \<and> card (agra g l) \<ge> 4 then 
                            (cgra g)(n := (efids_inc_ind(cgra g n)))
                      else (cgra g))
                                 (lgra g)
                    (if n \<in> ((agra g) l) \<and>  n \<notin> ((agra g) l') 
                        \<and> card (agra g l') \<ge> 3 \<and> card (agra g l) \<ge> 4 then
                       ((egra g)(l := (egra g l) - {efids_cur(cgra g n)}))
                                (l' := insert (efids_cur(efids_inc_ind(cgra g n)))(egra g l'))
                      else egra g)(kgra g)"

definition put_graph_efid :: "[identity, location, igraph] \<Rightarrow> igraph"
  where \<open>put_graph_efid n l g  \<equiv> Lgraph (gra g)(agra g)
                            ((cgra g)(n := efids_inc_ind(cgra g n)))
                               (lgra g)
                             ((egra g)(l := insert (efids_cur(efids_inc_ind(cgra g n)))
                                           ((egra g l) - {efids_cur(cgra g n)})))
                              (kgra g)\<close>

inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph G; enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get : "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G;
        enables I l (Actor a) get;
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)(egra G)
                       ((kgra G)(a := ((kgra G a)(l:= {(x,y). x \<in> agra G l \<and> y \<in> egra G l})))))
                   (delta I)
         \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| put : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> enables I l (Actor a) put \<Longrightarrow>
        I' = Infrastructure (put_graph_efid a l (graphI I))(delta I)
          \<Longrightarrow> I \<rightarrow>\<^sub>n I'"


text \<open>Note that the type infrastructure can now be instantiated to the axiomatic type class 
      @{text\<open>state\<close>} which enables the use of the underlying Kripke structures and CTL.\<close>
instantiation "infrastructure" :: state
begin
definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: infrastructure))"

instance
  by (rule MC.class.MC.state.of_class.intro)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"

end


lemma move_graph_eq: "move_graph_a a l l g = g"  
  by (simp add: move_graph_a_def, case_tac g, force)




definition ref_map :: "[InfrastructureThree.infrastructure, 
                        [InfrastructureTwo.igraph, location] \<Rightarrow> policy set]
                        \<Rightarrow> InfrastructureTwo.infrastructure"
  where "ref_map I lp = InfrastructureTwo.Infrastructure 
                                 (InfrastructureTwo.Lgraph
                                        (InfrastructureThree.gra (graphI I))
                                        (InfrastructureThree.agra (graphI I))
                                        (InfrastructureThree.cgra (graphI I))
                                        (InfrastructureThree.lgra (graphI I))
                                        (InfrastructureThree.egra (graphI I))
                                        (InfrastructureThree.kgra (graphI I)))   
                                                         lp"

lemma delta_invariant[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z')"
  apply clarify
  apply (erule state_transition_in.cases)
  by simp+


lemma same_actors0[rule_format]: "\<forall> z z'.  z \<rightarrow>\<^sub>n z' \<longrightarrow> actors_graph (graphI z) = actors_graph (graphI z')"
proof (clarify, erule state_transition_in.cases)
  show " \<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a a l l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z')"
    apply (simp add: InfrastructureThree.actors_graph_def)
    apply (rule equalityI)
     apply (rule subsetI)
     apply (rule CollectI)
     apply (drule CollectD)
     apply (erule exE, erule conjE)+
    apply (simp add: move_graph_a_def)
     apply (smt (z3) Collect_cong InfrastructureThree.gra.simps InfrastructureThree.nodes_def)
    apply (simp add: InfrastructureThree.enables_def move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
     apply (rule subsetI)
     apply (rule CollectI)
     apply (drule CollectD)
     apply (erule exE)+
     apply (erule conjE)+
 (*    apply (smt (z3) InfrastructureThree.gra.simps InfrastructureThree.nodes_def mem_Collect_eq) *)
    using InfrastructureThree.nodes_def by auto
next show " \<And>z z' G I a l I' g.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G) (InfrastructureThree.cgra G)
          (InfrastructureThree.lgra G) (InfrastructureThree.egra g)
          ((InfrastructureThree.kgra g)
           (a := (InfrastructureThree.kgra g a)
              (l := {(x, y). x \<in> InfrastructureThree.agra G l \<and> y \<in> InfrastructureThree.egra G l}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z')"
    by (simp add: InfrastructureThree.actors_graph_def InfrastructureThree.nodes_def)
next show "\<And>z z' G I a l I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a l (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z')"
    by (simp add: InfrastructureThree.actors_graph_def InfrastructureThree.nodes_def InfrastructureThree.put_graph_efid_def)
qed

lemma same_actors: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI I) = actors_graph(graphI y)"
proof (erule rtrancl_induct)
  show "actors_graph (graphI I) = actors_graph (graphI I)"
    by (rule refl)
next show "\<And>(y::infrastructure) z::infrastructure.
       (I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       actors_graph (graphI I) = actors_graph (graphI y) \<Longrightarrow>
       actors_graph (graphI I) = actors_graph (graphI z)"
    by (drule CollectD, simp, drule same_actors0, simp)  
qed

(* locations invariants *)
 lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
    apply clarify
  apply (erule InfrastructureThree.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def put_graph_efid_def)+

lemma same_nodes: "(c, s) \<in> {(x::InfrastructureThree.infrastructure, y::InfrastructureThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> InfrastructureThree.nodes (graphI c) = InfrastructureThree.nodes (graphI s)"
  apply (erule rtrancl_induct)
   apply (rule refl)
  apply (drule CollectD)
    apply simp
    apply (drule same_nodes0)
  by simp  

(* delta invariants *)
lemma init_state_policy0: "\<lbrakk> \<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z'); 
                          (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<rbrakk> \<Longrightarrow> 
                          delta(x) = delta(y)"  
  apply (rule mp)
  prefer 2
   apply (rotate_tac 1)
    apply assumption
  thm rtrancl_induct
  apply (erule rtrancl_induct)  
    apply (rule impI)
   apply (rule refl)
    apply (subgoal_tac "delta y = delta z")
   apply (erule impE)
    apply assumption
    apply (rule impI)
   apply (rule trans)
    apply assumption+
  apply (drule_tac x = y in spec)
  apply (drule_tac x = z in spec)
    apply (rotate_tac -1)
  apply (erule impE)
    apply simp
by assumption
 
lemma init_state_policy: "\<lbrakk> (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<rbrakk> \<Longrightarrow> 
                          delta(x) = delta(y)"  
  apply (rule init_state_policy0)
  apply clarify
    apply (rule delta_invariant)
  by assumption

lemma efids_list_eqO: " InfrastructureThree.efids_list (ef) =
       InfrastructureThree.efids_list  (InfrastructureThree.efids_inc_ind ef)"
  by (metis InfrastructureThree.efids_inc_ind.simps InfrastructureThree.efids_list.simps efidlist.exhaust)
 

lemma efids_list_eq[rule_format]: "(\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow> 
efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) =
efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a))"
proof (clarify, frule same_actors0, frule same_nodes0, erule state_transition_in.cases)
  show "\<And>z z' G I aa l l' I'.
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       aa \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a aa l l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) =
       InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)"
    using InfrastructureThree.efids_list_eqO InfrastructureThree.move_graph_a_def by fastforce
next show "\<And>z z' G I aa l I'.
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I l (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (aa := (InfrastructureThree.kgra G aa)
              (l := {(x, y). x \<in> InfrastructureThree.agra G l \<and> y \<in> InfrastructureThree.egra G l}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) =
       InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)"
    using InfrastructureThree.move_graph_a_def efids_list_eqO by fastforce
next show
 "\<And>z z' G I aa l I'.
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureThree.enables I l (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid aa l (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) =
       InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a) "
    apply (simp add: move_graph_a_def)
    using InfrastructureThree.put_graph_efid_def efids_list_eqO by fastforce
qed

lemma efids_list_eq0: "\<And> z z'. (z \<rightarrow>\<^sub>n z') \<Longrightarrow>
\<forall> a. efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) =
efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)"
  by (simp add: efids_list_eq)

lemma efids_list_eq_refl[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
\<forall> a. efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) =
efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a. InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) =
               InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a) \<Longrightarrow>
           \<forall>a. InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) =
               InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)"
    by (simp add: InfrastructureThree.efids_list_eq)
qed

(* *)
lemma efids_list_disjoint: "(\<forall> (z :: InfrastructureThree.infrastructure). (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
(range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a'))) = {}))
\<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z'). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z'). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a')))) = {})))
))"
    apply clarify
  apply (erule InfrastructureThree.state_transition_in.cases)
  apply (smt (z3) InfrastructureThree.efids_list_eq0 InfrastructureThree.same_actors0 InfrastructureThree.state_transition_in.move)
   apply (simp add: InfrastructureThree.actors_graph_def InfrastructureThree.nodes_def)
  apply (simp add: put_graph_efid_def)
  by (metis InfrastructureThree.graphI.simps InfrastructureThree.put_graph_efid_def InfrastructureThree.same_actors0 InfrastructureThree.state_transition_in.put efidlist.exhaust efids_inc_ind.simps efids_list.simps)

lemma ran_efidslist_disjoint:
"(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')))) = {})))
\<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z'). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z'). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a')))) = {})))
))"
  by (rule efids_list_disjoint)


lemma ran_efids_list_disjoint_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow>
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {}))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI y). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI y). a \<noteq> a' \<longrightarrow>
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a')))) = {})))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
              \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter>
                 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')) =
                 {} \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI y).
              \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI y).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)) \<inter>
                 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a')) =
                 {} \<Longrightarrow>
           \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
              \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
                 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
                 {}"
    by (simp add: ran_efidslist_disjoint)
qed



(* efids_cur inj_on*)
lemma efids_cur_in_efids_listO: "a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
           efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)
         \<in> range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))"
  apply (case_tac "(InfrastructureThree.cgra (InfrastructureThree.graphI I) a)")
  by simp

lemma efids_cur_in_efids_list: "a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
           efids_cur (efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))
         \<in> range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))"
  apply (case_tac "(InfrastructureThree.cgra (InfrastructureThree.graphI I) a)")
  by simp

lemma efids_list_inj_imp_inc_ind_not_eq[rule_format]: " (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
 inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<longrightarrow>
      efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)))"
proof (clarify, simp add: efids_inc_ind_def efids_cur_def efids_list_def, case_tac "InfrastructureThree.graphI z", simp)
  show "\<And>a x1 x2 x3 x4 x5 x6.
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.igraph.Lgraph x1 x2 x3 x4 x5 x6) \<Longrightarrow>
       inj (rec_efidlist (\<lambda>e n ef. ef) (x3 a)) \<Longrightarrow>
       rec_efidlist (\<lambda>e n ef. ef n) (x3 a) = rec_efidlist (\<lambda>e n ef. ef n) (rec_efidlist (\<lambda>e n. Efids e (Suc n)) (x3 a)) \<Longrightarrow>
       InfrastructureThree.graphI z = InfrastructureThree.igraph.Lgraph x1 x2 x3 x4 x5 x6 \<Longrightarrow> False"
    by (smt (z3) efidlist.exhaust efidlist.rec n_not_Suc_n the_inv_f_f)
qed

(* New invariant in step 3: card (agra g l) \<ge> 2 is preserved *)
lemma card_minusO: "3 \<le> card (S) \<Longrightarrow> 2 \<le> card (S - {a})"
  by (metis (no_types, lifting) Diff_empty Diff_insert0 Suc_le_mono card.infinite card.insert_remove insert_Diff insert_Diff_single le_0_eq le_trans nat_le_linear numeral_2_eq_2 numeral_3_eq_3)

lemma card_minus_gen: "Suc n \<le> k \<Longrightarrow> n \<le> k"
  by (erule Nat.Suc_leD)

lemma card_minus_diff: "card (S) \<le> Suc(card ( S - {a}))"
  by (metis Suc_le_lessD card_Diff1_less_iff card_Suc_Diff1 nat_le_linear)


lemma card_minus: "4 \<le> card (S) \<Longrightarrow> 3 \<le> card (S - {a})"
  apply (case_tac "a \<in> S")
  apply (smt (z3) Diff_idemp Suc_leI card.infinite card.insert_remove card_minusO dual_order.trans insert_Diff le_neq_implies_less nat.simps(3) nat_le_linear numeral_2_eq_2 numeral_3_eq_3 numeral_le_iff semiring_norm(69) semiring_norm(72))
  by force

lemma card_insertO:  "2 \<le> card S \<Longrightarrow> 2 \<le> card (insert a S)"
  by (metis card.infinite card_insert_le dual_order.trans le_zero_eq nat.simps(3) numeral_2_eq_2)

lemma card_insert:  "3 \<le> card S \<Longrightarrow> 3 \<le> card (insert a S)"
  by (metis One_nat_def Suc_leI Suc_le_lessD card.infinite card_insert_le dual_order.trans le_zero_eq nat.simps(3) numeral_le_iff numerals(1) semiring_norm(68))

lemma numbers_actors_inv: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  
(\<forall> l \<in> nodes (graphI z). card (agra (graphI z) l) \<ge> 3 \<longrightarrow> 
 card (agra (graphI z') l) \<ge> 3)"
proof (clarify, frule same_nodes0, erule state_transition_in.cases)
  show "\<And>z z' l G I a la l' I'.
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z) l) \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a a la l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z') l)"
    apply (simp add: InfrastructureThree.move_graph_a_def)
    by (metis One_nat_def card_Diff_singleton card_insert card_minus)
(*
    apply (rule conjI)
     apply (rule impI)+
    apply (rule conjI)
      apply (rule impI)+
    apply force
     apply (rule impI)+
     apply (erule conjE)+
    apply (erule card_minus)
     apply (rule impI)+
    apply (erule conjE)+
    by (erule card_insert)
*)
next show "\<And>z z' l G I a la I' g.
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z) l) \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra g)
          ((InfrastructureThree.kgra g)
           (a := (InfrastructureThree.kgra g a)
              (la := {(x, y). x \<in> InfrastructureThree.agra G la \<and> y \<in> InfrastructureThree.egra G la}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z') l)"
    by force
next show "\<And>z z' l G I a la I'.
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z) l) \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a la (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z') l)"
    using InfrastructureThree.put_graph_efid_def by force
qed

lemma numbers_actors_invO[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  
(\<forall> l \<in> nodes (graphI z). card (agra (graphI z) l) \<ge> 3 \<longrightarrow> 
 card (agra (graphI z') l) \<ge> 3)"
  using numbers_actors_inv by blast


(*
lemma numbers_actors_inv_old: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  
(\<forall> l \<in> nodes (graphI z). card (agra (graphI z) l) \<ge> 2 \<longrightarrow> 
 card (agra (graphI z') l) \<ge> 2)"
proof (clarify, frule same_nodes0, erule state_transition_in.cases)
  show "\<And>z z' l G I a la l' I'.
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       2 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z) l) \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a a la l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       2 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z') l)"
    apply (simp add: InfrastructureThree.move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
    apply (rule conjI)
      apply (rule impI)+
    apply force
     apply (rule impI)+
     apply (erule conjE)+
    apply (erule card_minus)
     apply (rule impI)+
    apply (erule conjE)+
    by (erule card_insert)
next show "\<And>z z' l G I a la I' g.
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       2 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z) l) \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra g)
          ((InfrastructureThree.kgra g)
           (a := (InfrastructureThree.kgra g a)
              (la := {(x, y). x \<in> InfrastructureThree.agra G la \<and> y \<in> InfrastructureThree.egra G la}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       2 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z') l)"
    by force
next show "\<And>z z' l G I a la I'.
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       2 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z) l) \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a la (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       2 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z') l)"
    using InfrastructureThree.put_graph_efid_def by force
qed
*)

lemma  numbers_actors_inv_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
            l \<in> nodes (graphI I) \<Longrightarrow> card (agra (graphI I) l) \<ge> 3 \<Longrightarrow> card (agra (graphI y) l) \<ge> 3"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<Longrightarrow>
           3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI I) l) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI y) l) \<Longrightarrow>
           3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI z) l)"
    by (simp add: InfrastructureThree.same_nodes numbers_actors_inv)
qed


(* Adopt the agra \<longrightarrow> egra invariants from Level Two *) 
lemma actor_unique_loc_lem00[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l')) 
        \<longrightarrow> (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z') \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z') l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z') l' \<longrightarrow> l = l'))"
  apply (rule allI)+
  apply (rule impI)+
  apply (erule InfrastructureThree.state_transition_in.cases)
    apply (simp add: move_graph_a_def)
  apply auto[1]
  using InfrastructureThree.agra.simps InfrastructureThree.graphI.simps apply presburger
  using InfrastructureThree.agra.simps InfrastructureThree.graphI.simps InfrastructureThree.put_graph_efid_def by presburger


lemma actor_unique_loc_lem0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  (\<forall> l'. l' \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow> 
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l'))) 
        \<longrightarrow> (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z') \<longrightarrow>  (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z') l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z') l' \<longrightarrow> l = l')))"
  apply (rule allI)+
  apply (rule impI)+
  apply (erule InfrastructureThree.state_transition_in.cases)
    apply (simp add: move_graph_a_def)
  using InfrastructureThree.atI_def apply force
  using InfrastructureThree.agra.simps InfrastructureThree.graphI.simps apply presburger
  using InfrastructureThree.agra.simps InfrastructureThree.graphI.simps InfrastructureThree.put_graph_efid_def by presburger
thm actor_unique_loc_lem0

lemma actor_unique_loc_lem0a: "z \<rightarrow>\<^sub>n z' \<Longrightarrow>  nodes (graphI z) = nodes (graphI z') \<Longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l'))
        \<Longrightarrow> l \<in> nodes (graphI z') \<Longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z') l \<Longrightarrow> 
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z') l' \<Longrightarrow> l = l'"
  using actor_unique_loc_lem00 by presburger

lemma actor_unique_loc_lem[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI y) \<longrightarrow> 
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI y) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI y) l' \<longrightarrow> l = l'))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a l l'.
              l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI y) \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI y) l \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI y) l' \<longrightarrow> l = l' \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l'"
    by (metis CollectD InfrastructureThree.same_nodes actor_unique_loc_lem0a case_prodD rtrancl.rtrancl_into_rtrancl)
qed


lemma efid_in_range_invariantO: "(\<forall> (z :: InfrastructureThree.infrastructure) z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow> 
         (\<forall> l \<in> InfrastructureThree.nodes (graphI z).
         (\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z) l).
         (\<exists> a \<in> InfrastructureThree.actors_graph (graphI z). e \<in> range (efids_list (InfrastructureThree.cgra (graphI z) a)))))
          \<longrightarrow>  (\<forall> l \<in> nodes (graphI z').
         (\<forall> e \<in> (egra (InfrastructureThree.graphI z') l). 
         (\<exists> a \<in> actors_graph (graphI z'). e \<in> range (efids_list (InfrastructureThree.cgra (graphI z') a))))))"
proof (clarify, frule same_actors0, frule same_nodes0, frule efids_list_eq0, erule state_transition_in.cases)
show "\<And>z z' l e G I a la I'.
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
                e \<in> range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       e \<in> InfrastructureThree.egra (InfrastructureThree.graphI z') l \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) = InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       \<forall>a. InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) =
           InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G) (InfrastructureThree.cgra G)
          (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (a := (InfrastructureThree.kgra G a)
              (la := {(x, y). x \<in> InfrastructureThree.agra G la \<and> y \<in> InfrastructureThree.egra G la}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z').
          e \<in> range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a))"
    by simp
next show "\<And>z z' l e G I a la l' I'.
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
                e \<in> range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       e \<in> InfrastructureThree.egra (InfrastructureThree.graphI z') l \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       \<forall>a. InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) =
           InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a a la l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z').
          e \<in> range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a))"
    apply (unfold move_graph_a_def)
    by (smt (z3) DiffD1 InfrastructureThree.cgra.simps InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.egra.simps InfrastructureThree.graphI.simps fun_upd_def insertE)
  next show " \<And>z z' l e G I a la I'.
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
                e \<in> range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       e \<in> InfrastructureThree.egra (InfrastructureThree.graphI z') l \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       \<forall>a. InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) =
           InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a la (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z').
          e \<in> range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z') a))"
    apply (simp add: move_graph_a_def)
      by (smt (verit, best) DiffD1 InfrastructureThree.actors_graph_def InfrastructureThree.atI_def InfrastructureThree.efids_cur_in_efids_list InfrastructureThree.egra.simps InfrastructureThree.put_graph_efid_def fun_upd_def insert_iff mem_Collect_eq)
qed

(* variation for applicability*)
lemma efid_in_range_invariantOa: "(z \<rightarrow>\<^sub>n z') \<Longrightarrow> 
         (\<forall> l \<in> nodes (graphI z).
         (\<forall> e \<in> (egra (InfrastructureThree.graphI z) l).
         (\<exists> a \<in> actors_graph (graphI z). e \<in> range (efids_list (InfrastructureThree.cgra (graphI z) a)))))
          \<Longrightarrow>  (\<forall> l \<in> nodes (graphI z').
         (\<forall> e \<in> (egra (InfrastructureThree.graphI z') l). 
         (\<exists> a \<in> actors_graph (graphI z'). e \<in> range (efids_list (InfrastructureThree.cgra (graphI z') a)))))"
  using efid_in_range_invariantO by presburger

lemma efids_in_range_invariantOO[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
        \<Longrightarrow> (\<forall> l \<in> nodes (graphI I).
            \<forall> e \<in> (egra (InfrastructureThree.graphI I) l).
         \<exists> a \<in> actors_graph (graphI I). e \<in> range (efids_list (InfrastructureThree.cgra (graphI I) a)))
       \<Longrightarrow> (\<forall> l \<in> nodes (graphI y).
           \<forall> e \<in> (egra (InfrastructureThree.graphI y) l).
         \<exists> a \<in> actors_graph (graphI y). e \<in> range (efids_list (InfrastructureThree.cgra (graphI y) a)))"
proof (erule rtrancl_induct)
  show "\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI I) l.
          \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
             e \<in> range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<Longrightarrow>
    \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI I) l.
          \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
             e \<in> range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))"
    by blast
next show "\<And>y z. \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
              \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI I) l.
                 \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
                    e \<in> range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI y).
              \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI y) l.
                 \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI y).
                    e \<in> range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)) \<Longrightarrow>
           \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
              \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
                 \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
                    e \<in> range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) "
    using efid_in_range_invariantO by auto
qed


(* Adopt the efids_cur and egra lemmas from Level Two *)
lemma efids_cur_eq_egra[rule_format]: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI z).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI z) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI z').
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z') l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI z') l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)))))"
proof (clarify, frule same_actors0, frule same_nodes0, rule state_transition_in.cases, assumption)
  show "\<And>z z' l e G I a la l' I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       e \<in> InfrastructureThree.egra (InfrastructureThree.graphI z') l \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) = InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a a la l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l.
          e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)"
    apply (simp add: move_graph_a_def)
    by (smt (z3) DiffE Diff_empty Diff_insert0 fun_upd_other fun_upd_same insertE insert_Diff1 mk_disjoint_insert singleton_iff)
next show "\<And>z z' l e G I a la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       e \<in> InfrastructureThree.egra (InfrastructureThree.graphI z') l \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) = InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I la (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G) (InfrastructureThree.cgra G)
          (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (a := (InfrastructureThree.kgra G a)
              (la := {(x, y). x \<in> InfrastructureThree.agra G la \<and> y \<in> InfrastructureThree.egra G la}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l.
          e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)"
    by simp
next show "\<And>z z' l e G I a la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       e \<in> InfrastructureThree.egra (InfrastructureThree.graphI z') l \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a la (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l.
          e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)"
    apply (unfold put_graph_efid_def)
    apply (case_tac "l = la")
    apply (smt (z3) DiffE InfrastructureThree.agra.simps InfrastructureThree.atI_def InfrastructureThree.cgra.simps InfrastructureThree.egra.simps InfrastructureThree.graphI.simps fun_upd_apply insertCI insertE)
    apply (drule_tac x = l in bspec)
     apply metis
    apply (subgoal_tac "e \<in> InfrastructureThree.egra (InfrastructureThree.graphI z) l ")
    prefer 2
    apply fastforce
    apply (drule_tac x = e in bspec, assumption)
    apply (erule bexE)
    apply (rule_tac x = aa in bexI)
     apply (simp add: atI_def)
     apply (subgoal_tac "aa \<noteq> a")
      apply simp
    prefer 2
    using InfrastructureThree.agra.simps InfrastructureThree.graphI.simps apply presburger
    by meson
qed

lemma efids_cur_eq_egra_refl[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI I).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI I) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI I) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI y).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI y) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI y) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a l l'.
              l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           (\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
               \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI I) l.
                  \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI I) l.
                     e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<longrightarrow>
           (\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI y).
               \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI y) l.
                  \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI y) l.
                     e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)) \<Longrightarrow>
           (\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
               \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI I) l.
                  \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI I) l.
                     e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<longrightarrow>
           (\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
               \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
                  \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                     e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))"
    by (simp add: Pair_inject actor_unique_loc_lem case_prodE efids_cur_eq_egra)
  qed

(* efids_cur injective*)
lemma efids_cur_inj_on_inv0[rule_format]: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')))) = {}))) \<longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
      efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI z) x)) 
           (actors_graph (InfrastructureThree.graphI z)) \<longrightarrow> 
     inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI z') x))
           (actors_graph (InfrastructureThree.graphI z')))))"
  by (smt (verit, ccfv_SIG) InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.ran_efidslist_disjoint disjoint_iff inj_on_def)


lemma efids_cur_inj_on_inv_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {}))) \<Longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
      efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI I) x)) 
           (actors_graph (InfrastructureThree.graphI I))) \<Longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI y) x)) 
           (actors_graph (InfrastructureThree.graphI y)))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
              \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter>
                 range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')) =
                 {} \<Longrightarrow>
           \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
              InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) \<noteq>
              InfrastructureThree.efids_cur
               (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<Longrightarrow>
           inj_on (\<lambda>x. InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) x))
            (InfrastructureThree.actors_graph (InfrastructureThree.graphI I)) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           inj_on (\<lambda>x. InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI y) x))
            (InfrastructureThree.actors_graph (InfrastructureThree.graphI y)) \<Longrightarrow>
           inj_on (\<lambda>x. InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) x))
            (InfrastructureThree.actors_graph (InfrastructureThree.graphI z)) "
    by (smt (verit, del_insts) InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.efids_list_eq InfrastructureThree.ran_efids_list_disjoint_refl InfrastructureThree.same_actors0 Int_iff case_prod_conv empty_iff inj_on_def mem_Collect_eq)
qed

(* Invariant for refmapTwo_lem -- maybe also useful here ? *)
lemma refmap_lem_egra_unique_prepO: "(\<forall> l \<in> nodes(InfrastructureThree.graphI z).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI z) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)))
\<Longrightarrow> (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l')) 
\<Longrightarrow> (inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI z) x)) 
           (actors_graph (InfrastructureThree.graphI z)))
\<Longrightarrow>  (\<forall> a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z). 
     (\<forall> l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z). 
       (\<forall> l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z). 
             (a @\<^bsub>(InfrastructureThree.graphI z)\<^esub> l) \<longrightarrow>
        (InfrastructureOne.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)
       \<in> InfrastructureThree.egra (InfrastructureThree.graphI z) l') 
       \<longrightarrow> l = l' )))"
  apply clarify
  apply (drule_tac x = l' in bspec, assumption)
  apply (rotate_tac -1)
  apply (drule_tac x = "InfrastructureOne.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)" in bspec, assumption)
  apply (erule bexE)
  apply (simp add: atI_def)
  apply (subgoal_tac "a = aa")
   apply blast
  apply (erule inj_onD)
    apply (subgoal_tac " InfrastructureOne.efids_cur =  InfrastructureThree.efids_cur")
     prefer 2
    apply (simp add: InfrastructureOne.efids_cur_def  InfrastructureThree.efids_cur_def)
    apply simp
  apply blast
  using InfrastructureThree.actors_graph_def by blast


lemma refmap_lem_egra_unique_refl[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI I).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI I) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI I) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)))
\<Longrightarrow> (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {}))) \<Longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
      efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)))
\<Longrightarrow> (inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI I) x)) 
           (actors_graph (InfrastructureThree.graphI I)))
\<Longrightarrow>  (\<forall> a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI y). 
     (\<forall> l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI y). 
       (\<forall> l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI y). 
             (a @\<^bsub>(InfrastructureThree.graphI y)\<^esub> l) \<longrightarrow>
        (InfrastructureOne.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)
       \<in> InfrastructureThree.egra (InfrastructureThree.graphI y) l') 
       \<longrightarrow> l = l' )))"
  apply (rule refmap_lem_egra_unique_prepO)
  apply (simp add: InfrastructureThree.efids_cur_eq_egra_refl)
  using InfrastructureThree.actor_unique_loc_lem apply presburger
  by (rule efids_cur_inj_on_inv_refl, assumption+)


(* global policy lemmas:
  (a) The disjointness of kgras can be shown from disjointness of egras and does imply (see CoronaAppTwo)
   that non idenitifability holds for subsets L \<subseteq> nodes (graphI I) bigger than 2.
  (b) If there are always three at each location also singleton intersections cannot become identifiable. *)

(* Disjointness of egras can be derived step by step and then with induction exrapolated to 
   all reachable sets. This is used to show kgra disjointness*)
lemma no_elem_inter_disjoint: "~(\<exists> x. x \<in> A \<and> x \<in> B) \<Longrightarrow> A \<inter> B = {}"
  by blast


lemma all_egra_disjoint[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')))) = {}))) \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI z).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI z) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
  (\<forall> a \<in> actors_graph  (graphI z).  
     (\<forall> l \<in> nodes (graphI z). \<forall> l' \<in> nodes (graphI z). 
         (l \<noteq> l' \<longrightarrow> (egra (graphI z) l) \<inter> egra(graphI z) l' = {}))) \<longrightarrow>
  (\<forall> a \<in> actors_graph  (graphI z'). 
     (\<forall> l \<in> nodes (graphI z'). \<forall> l' \<in> nodes (graphI z'). 
         (l \<noteq> l' \<longrightarrow> (egra (graphI z') l) \<inter> egra(graphI z') l' = {})))"
proof (clarify, frule same_actors0, frule same_nodes0, rule state_transition_in.cases, assumption)
  show "\<And>z z' a l l' G I aa la l'a I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
             a \<noteq> a' \<longrightarrow>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
             {} \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
             \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                l \<noteq> l' \<longrightarrow>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                {} \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l'a \<in> InfrastructureThree.nodes G \<Longrightarrow>
       aa \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l'a (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a aa la l'a (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l \<inter>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l' =
       {}"
    apply (rule no_elem_inter_disjoint)
    apply (rule notI)
    apply (erule exE, erule conjE)
    apply (subgoal_tac " \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z').
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z') l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a) ")
     prefer 2
     apply (metis InfrastructureThree.efids_cur_eq_egra)
    apply (subgoal_tac "\<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l.
                x = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)")
    apply (subgoal_tac "\<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l'.
                x = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)")
    prefer 2
      apply meson
    prefer 2
     apply meson
    apply (erule bexE)+
    apply (subgoal_tac "ab \<noteq> ac")
    prefer 2
     apply (meson InfrastructureThree.actor_unique_loc_lem00)
    by (metis (no_types, lifting) InfrastructureThree.actors_graph_def InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.efids_list_eq InfrastructureThree.ran_efids_list_disjoint_refl Int_iff empty_iff mem_Collect_eq rtrancl.simps)
next show "\<And>z z' a l l' G I aa la I'.
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
             a \<noteq> a' \<longrightarrow>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
             {} \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
             \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                l \<noteq> l' \<longrightarrow>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                {} \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I la (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (aa := (InfrastructureThree.kgra G aa)
              (la := {(x, y). x \<in> InfrastructureThree.agra G la \<and> y \<in> InfrastructureThree.egra G la}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l \<inter>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l' =
       {}"
    by (smt (z3) Collect_cong InfrastructureThree.actors_graph_def InfrastructureThree.agra.simps InfrastructureThree.egra.simps InfrastructureThree.graphI.simps)
next show "\<And>z z' a l l' G I aa la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
             a \<noteq> a' \<longrightarrow>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
             {} \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
             \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                l \<noteq> l' \<longrightarrow>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                {} \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid aa la (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l \<inter>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l' =
       {}"
    apply (rule no_elem_inter_disjoint)
    apply (rule notI)
    apply (erule exE, erule conjE)
    apply (subgoal_tac " \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z').
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z') l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a) ")
     prefer 2
     apply (metis InfrastructureThree.efids_cur_eq_egra)
    apply (subgoal_tac "\<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l.
                x = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)")
    apply (subgoal_tac "\<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l'.
                x = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)")
    prefer 2
      apply meson
    prefer 2
     apply meson
    apply (erule bexE)+
    apply (subgoal_tac "ab \<noteq> ac")
    prefer 2
     apply (meson InfrastructureThree.actor_unique_loc_lem00)
    by (metis (no_types, lifting) InfrastructureThree.actors_graph_def InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.efids_list_eq InfrastructureThree.ran_efids_list_disjoint_refl Int_iff empty_iff mem_Collect_eq rtrancl.simps)
qed

lemma all_egra_disjoint_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {}))) \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI I).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI I) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI I) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
  (\<forall> a \<in> actors_graph  (graphI I).  
     (\<forall> l \<in> nodes (graphI I). \<forall> l' \<in> nodes (graphI I). 
         (l \<noteq> l' \<longrightarrow> (egra (graphI I) l) \<inter> egra(graphI I) l' = {}))) \<longrightarrow>
  (\<forall> a \<in> actors_graph  (graphI y). 
     (\<forall> l \<in> nodes (graphI y). \<forall> l' \<in> nodes (graphI y). 
         (l \<noteq> l' \<longrightarrow> (egra (graphI y) l) \<inter> egra(graphI y) l' = {})))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
              \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter>
                 range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')) =
                 {} \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
              \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI I) l.
                 \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI I) l.
                    e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           (\<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
               \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
                  \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
                     l \<noteq> l' \<longrightarrow>
                     InfrastructureThree.egra (InfrastructureThree.graphI I) l \<inter>
                     InfrastructureThree.egra (InfrastructureThree.graphI I) l' =
                     {}) \<longrightarrow>
           (\<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI y).
               \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI y).
                  \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI y).
                     l \<noteq> l' \<longrightarrow>
                     InfrastructureThree.egra (InfrastructureThree.graphI y) l \<inter>
                     InfrastructureThree.egra (InfrastructureThree.graphI y) l' =
                     {}) \<Longrightarrow>
           (\<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
               \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
                  \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
                     l \<noteq> l' \<longrightarrow>
                     InfrastructureThree.egra (InfrastructureThree.graphI I) l \<inter>
                     InfrastructureThree.egra (InfrastructureThree.graphI I) l' =
                     {}) \<longrightarrow>
           (\<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
               \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                  \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                     l \<noteq> l' \<longrightarrow>
                     InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                     InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                     {})"
    thm all_egra_disjoint
    apply clarify
    apply (rule all_egra_disjoint, assumption)
    apply (metis InfrastructureThree.ran_efids_list_disjoint_refl)
    using InfrastructureThree.actor_unique_loc_lem apply presburger
    apply (simp add: InfrastructureThree.efids_cur_eq_egra_refl)
        apply meson
   by assumption+
qed

(* For the proof of kgra intersections are empty, we prove the  
   Lemma_star_star that generalizes all_egra_disjoint(_refl) to different z and z' with
   z \<rightarrow>* z' where I \<rightarrow>* z.
   To that end we can use the Lemma_star:
   forall y. I \<rightarrow>* y \<longrightarrow> \forall a \in actors_graph I.
    efids_cur(efids_inc_ind (egra y a)) \<notin>
   Union {egra z l |z l. I \<rightarrow>* z \<and> z \<rightarrow>* y \<and> l \<in> nodes z}
    *)
(*use efids_list_inj_imp_inc_ind_not_eq, efids_cur_in_efids_list ... *)
lemma lemma_starOOO:
"(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')))) = {}))) \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI z).
 \<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI z) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)))  \<Longrightarrow>
 inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<Longrightarrow>
l \<in> nodes (graphI z) \<Longrightarrow> 
a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l \<Longrightarrow>
InfrastructureThree.efids_cur
        (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))
       \<notin> InfrastructureThree.egra (InfrastructureThree.graphI z) l"
  by (metis (mono_tags, lifting) InfrastructureThree.actors_graph_def InfrastructureThree.efids_cur_in_efids_list InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.efids_list_inj_imp_inc_ind_not_eq Int_iff empty_iff mem_Collect_eq)

lemma lemma_starOOO':
"(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')))) = {}))) \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI z).
 \<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI z) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)))  \<Longrightarrow>
 inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<Longrightarrow>
l \<in> nodes (graphI z) \<Longrightarrow> 
a \<in>  actors_graph (InfrastructureThree.graphI z) \<Longrightarrow>
InfrastructureThree.efids_cur
        (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))
       \<notin> InfrastructureThree.egra (InfrastructureThree.graphI z) l"
  by (metis (mono_tags, lifting) InfrastructureThree.actors_graph_def InfrastructureThree.efids_cur_in_efids_list InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.efids_list_inj_imp_inc_ind_not_eq Int_iff empty_iff mem_Collect_eq)


lemma lemma_star_starO[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> 
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')))) = {}))) \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI z).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI z) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
     inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
  (\<forall> a \<in> actors_graph  (graphI z).  
     (\<forall> l \<in> nodes (graphI z). \<forall> l' \<in> nodes (graphI z). 
         (l \<noteq> l' \<longrightarrow> (egra (graphI z) l) \<inter> egra(graphI z) l' = {}))) \<longrightarrow>
 (\<forall> a \<in> actors_graph  (graphI z).  
     (\<forall> l \<in> nodes (graphI z). \<forall> l' \<in> nodes (graphI z). 
         (l \<noteq> l' \<longrightarrow> (egra (graphI z) l) \<inter> egra(graphI z') l' = {})))"
proof (clarify, frule same_actors0, frule same_nodes0, rule state_transition_in.cases, assumption)
  show "\<And>z z' a l l' G I aa la l'a I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
             a \<noteq> a' \<longrightarrow>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
             {} \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
             \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                l \<noteq> l' \<longrightarrow>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                {} \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l'a \<in> InfrastructureThree.nodes G \<Longrightarrow>
       aa \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l'a (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a aa la l'a (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l' =
       {}"
    apply (subgoal_tac "       InfrastructureThree.efids_cur
        (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI I) aa))
       \<notin> InfrastructureThree.egra (InfrastructureThree.graphI I) l")
    prefer 2
       apply (rule lemma_starOOO', simp, simp, simp, simp, simp)

    apply (simp add: actors_graph_def atI_def efids_list_eq efids_cur_in_efids_listO move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
    apply (rule conjI)
     apply (rule impI)+
    apply (rule conjI)
     apply (rule impI)+
    apply force
    apply meson
    apply (metis (no_types, lifting) Diff_empty Diff_insert0 disjoint_insert(2) insert_Diff)
     apply (rule impI)+
    apply (rule conjI)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply meson
    apply meson
      apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
    apply meson
    by meson
next show "\<And>z z' a l l' G I aa la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
             a \<noteq> a' \<longrightarrow>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
             {} \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
             \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                l \<noteq> l' \<longrightarrow>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                {} \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I la (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (aa := (InfrastructureThree.kgra G aa)
              (la := {(x, y). x \<in> InfrastructureThree.agra G la \<and> y \<in> InfrastructureThree.egra G la}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l' =
       {}"
    by (metis InfrastructureThree.egra.simps InfrastructureThree.graphI.simps)
next show "\<And>z z' a l l' G I aa la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
             a \<noteq> a' \<longrightarrow>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
             {} \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
             \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                l \<noteq> l' \<longrightarrow>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                {} \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid aa la (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l' =
       {}"
    by (smt (z3) DiffD1 InfrastructureThree.actors_graph_def InfrastructureThree.atI_def InfrastructureThree.cgra.simps InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.efids_list_eq InfrastructureThree.egra.simps InfrastructureThree.graphI.simps InfrastructureThree.put_graph_efid_def disjoint_iff fun_upd_def insert_iff mem_Collect_eq)
qed

lemma lemma_star_starO'[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> 
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')))) = {}))) \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI z).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI z) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
     inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
  (\<forall> a \<in> actors_graph  (graphI z).  
     (\<forall> l \<in> nodes (graphI z). \<forall> l' \<in> nodes (graphI z). 
         (l \<noteq> l' \<longrightarrow> (egra (graphI z) l) \<inter> egra(graphI z) l' = {}))) \<longrightarrow>
 (\<forall> a \<in> actors_graph  (graphI z).  
     (\<forall> l \<in> nodes (graphI z). \<forall> l' \<in> nodes (graphI z'). 
         (l \<noteq> l' \<longrightarrow> (egra (graphI z) l) \<inter> egra(graphI z') l' = {})))"
proof (clarify, frule same_actors0, frule same_nodes0, rule state_transition_in.cases, assumption)
  show " \<And>z z' a l l' G I aa la l'a I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
             a \<noteq> a' \<longrightarrow>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
             {} \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
             \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                l \<noteq> l' \<longrightarrow>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                {} \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l'a \<in> InfrastructureThree.nodes G \<Longrightarrow>
       aa \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l'a (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a aa la l'a (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l' =
       {}"
    apply (subgoal_tac "       InfrastructureThree.efids_cur
        (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI I) aa))
       \<notin> InfrastructureThree.egra (InfrastructureThree.graphI I) l")
    prefer 2
       apply (rule lemma_starOOO', simp, simp, simp, simp, simp)

    apply (simp add: actors_graph_def atI_def efids_list_eq efids_cur_in_efids_listO move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
    apply (rule conjI)
     apply (rule impI)+
    apply (rule conjI)
     apply (rule impI)+
    apply force
    apply meson
    apply (metis (no_types, lifting) Diff_empty Diff_insert0 disjoint_insert(2) insert_Diff)
     apply (rule impI)+
    apply (rule conjI)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply meson
    apply meson
      apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
    apply meson
    by meson
next show "\<And>z z' a l l' G I aa la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
             a \<noteq> a' \<longrightarrow>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
             {} \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
             \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                l \<noteq> l' \<longrightarrow>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                {} \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I la (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (aa := (InfrastructureThree.kgra G aa)
              (la := {(x, y). x \<in> InfrastructureThree.agra G la \<and> y \<in> InfrastructureThree.egra G la}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l' =
       {}"
    by (metis InfrastructureThree.egra.simps InfrastructureThree.graphI.simps)
next show "\<And>z z' a l l' G I aa la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
             a \<noteq> a' \<longrightarrow>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter>
             range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a')) =
             {} \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z) l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z) l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<Longrightarrow>
       \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI z).
          \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
             \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
                l \<noteq> l' \<longrightarrow>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
                InfrastructureThree.egra (InfrastructureThree.graphI z) l' =
                {} \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI z) \<Longrightarrow>
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z') \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI z) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureThree.enables I la (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid aa la (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.egra (InfrastructureThree.graphI z) l \<inter>
       InfrastructureThree.egra (InfrastructureThree.graphI z') l' =
       {}"
    by (smt (z3) DiffD1 InfrastructureThree.actors_graph_def InfrastructureThree.atI_def InfrastructureThree.cgra.simps InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.efids_list_eq InfrastructureThree.egra.simps InfrastructureThree.graphI.simps InfrastructureThree.put_graph_efid_def disjoint_iff fun_upd_def insert_iff mem_Collect_eq)
qed

lemma efids_index_efids_cur: "efids_list(cgra (graphI I) a)(efids_index (cgra (graphI I) a)) = 
                              efids_cur (cgra (graphI I) a)"
  by (metis InfrastructureThree.efids_cur.simps InfrastructureThree.efids_index.simps InfrastructureThree.efids_list.simps efidlist.exhaust)

lemma efids_inc_ind_Suc: "efids_index(efids_inc_ind(cgra (graphI I) a)) = Suc (efids_index(cgra(graphI I) a))"
  by (metis InfrastructureThree.efids_inc_ind.simps InfrastructureThree.efids_index.simps efidlist.exhaust)


lemma efids_index_leqOO: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> 
                    efids_index(cgra (graphI z) a) \<le> efids_index(cgra (graphI z') a)"
proof (clarify, rule state_transition_in.cases, assumption)
  show "\<And>z z' G I aa l l' I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       aa \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a aa l l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)
       \<le> InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)"
    by (simp add: InfrastructureThree.move_graph_a_def efids_inc_ind_Suc)
next show "\<And>z z' G I aa l I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I l (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (aa := (InfrastructureThree.kgra G aa)
              (l := {(x, y). x \<in> InfrastructureThree.agra G l \<and> y \<in> InfrastructureThree.egra G l}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)
       \<le> InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI z') a)"
    by force
next show "\<And>z z' G I aa l I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureThree.enables I l (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid aa l (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)
       \<le> InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI z') a) "
    by (simp add: InfrastructureThree.put_graph_efid_def efids_inc_ind_Suc)
qed



lemma efids_index_leqO: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                    efids_index(cgra (graphI I) a) \<le> efids_index(cgra (graphI y) a)"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)
           \<le> InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI y) a) \<Longrightarrow>
           InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)
           \<le> InfrastructureThree.efids_index (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)"
    by (metis CollectD case_prodD efids_index_leqOO order_trans)
qed

lemma efids_index_leq: "\<forall> z'. (InfrastructureThree.state_transition_in_refl I z') \<longrightarrow> 
                       (InfrastructureThree.state_transition_in_refl z' y) \<longrightarrow> 
                        efids_index(cgra (graphI z') a) \<le> efids_index(cgra (graphI y) a)"
  using InfrastructureThree.state_transition_in_refl_def efids_index_leqO by auto

lemma lemmaD: 
  assumes a0:"InfrastructureThree.state_transition_in_refl I y"
  and a0a : " a \<in> actors_graph (InfrastructureThree.graphI I)"
  and    a1: "(\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)))"
  and a1a: "(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l'))"
  and a1b: "(\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow>
            ((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
            (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {})))"
  and a2: " (\<forall> l \<in> nodes(InfrastructureThree.graphI I).
             \<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI I) l).
             (\<exists> a \<in> agra (InfrastructureThree.graphI I) l. 
                  e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)))"
  shows "efids_cur(efids_inc_ind(cgra (graphI y) a)) \<notin> 
                  {x. (\<exists> z l. x \<in> egra (graphI z) l \<and> (InfrastructureThree.state_transition_in_refl I z) \<and> 
                       (InfrastructureThree.state_transition_in_refl z y) \<and> l \<in> nodes (graphI I))}"
  using assms
proof -
  have "\<forall> x \<in> {x. (\<exists> z l. x \<in> egra (graphI z) l \<and> (InfrastructureThree.state_transition_in_refl I z) \<and> 
                       (InfrastructureThree.state_transition_in_refl z y) \<and> l \<in> nodes (graphI I))}.
          x \<noteq> efids_cur(efids_inc_ind(cgra (graphI y) a))" 
    apply (rule ballI)
    apply simp
    apply (erule exE)+
    apply (erule conjE)+
    apply (subgoal_tac "(\<forall> l \<in> nodes(InfrastructureThree.graphI z).
             \<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z) l).
             (\<exists> a \<in> agra (InfrastructureThree.graphI z) l. 
                  e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)))")
    apply (subgoal_tac "(\<exists> a' \<in> agra (InfrastructureThree.graphI z) l. 
     x = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a'))")
     prefer 2
    using InfrastructureThree.same_nodes InfrastructureThree.state_transition_in_refl_def apply blast
     prefer 2
    apply (simp add: InfrastructureThree.efids_cur_eq_egra_refl InfrastructureThree.state_transition_in_refl_def a1a a2)
    apply (erule bexE)
    apply (case_tac "a = a'")
     prefer 2
(* a \<noteq> a'*)
    apply (subgoal_tac "InfrastructureThree.efids_cur
        (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)) 
        \<in> range(efids_list (cgra (graphI y) a))")
      apply (subgoal_tac "x \<in> (range(efids_list (cgra (graphI z) a')))")
       apply (subgoal_tac "efids_list (cgra (graphI y) a') = efids_list (cgra (graphI z) a')")
        apply (subgoal_tac "(
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a')))) = {}))")
         apply (metis disjoint_insert(2) insert_Diff)
        apply (subgoal_tac "(\<forall> a \<in> actors_graph (InfrastructureThree.graphI y). 
      (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI y). a \<noteq> a' \<longrightarrow>
((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)) \<inter> 
 (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI y) a')))) = {})))")
    apply (metis (mono_tags, lifting) InfrastructureThree.actors_graph_def InfrastructureThree.same_actors InfrastructureThree.same_nodes InfrastructureThree.state_transition_in_refl_def a0a mem_Collect_eq)
    apply (simp add: InfrastructureThree.ran_efids_list_disjoint_refl InfrastructureThree.state_transition_in_refl_def a1b)
    thm efids_list_eq_refl
    apply (metis InfrastructureThree.state_transition_in_refl_def efids_list_eq_refl)
    using InfrastructureThree.actors_graph_def InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.same_nodes InfrastructureThree.state_transition_in_refl_def apply blast
    apply (metis InfrastructureThree.efids_cur_in_efids_list InfrastructureThree.same_actors InfrastructureThree.state_transition_in_refl_def a0a)
(* a = a'*)
    apply (subgoal_tac "\<forall> z'. (InfrastructureThree.state_transition_in_refl I z') \<longrightarrow> 
                       (InfrastructureThree.state_transition_in_refl z' y) \<longrightarrow> 
                        efids_index(cgra (graphI z') a) \<le> efids_index(cgra (graphI y) a)")
     prefer 2
    using efids_index_leq apply presburger
    apply (subgoal_tac "\<forall> z'. (InfrastructureThree.state_transition_in_refl I z') \<longrightarrow> 
                       (InfrastructureThree.state_transition_in_refl z' y) \<longrightarrow> 
                   efids_index(efids_inc_ind(cgra (graphI y) a)) \<noteq> efids_index(cgra (graphI z') a)")
    prefer 2
     apply (metis Suc_n_not_le_n efids_inc_ind_Suc)
    apply (subgoal_tac "\<forall> z'. (InfrastructureThree.state_transition_in_refl I z') \<longrightarrow> 
                       (InfrastructureThree.state_transition_in_refl z' y) \<longrightarrow> 
                   efids_list(cgra (graphI y) a)(efids_index(efids_inc_ind(cgra (graphI y) a)))
                 \<noteq> efids_list(cgra (graphI y) a)(efids_index(cgra (graphI z') a))")
    prefer 2
    apply (metis InfrastructureThree.state_transition_in_refl_def a0a a1 efids_list_eq_refl the_inv_f_f)
    by (metis InfrastructureThree.efids_cur.simps InfrastructureThree.efids_inc_ind.simps InfrastructureThree.efids_index.simps InfrastructureThree.efids_list.simps InfrastructureThree.state_transition_in_refl_def efidlist.exhaust efids_list_eq_refl)
  from this show ?thesis by force
qed

lemma lemmaDO:  
 "InfrastructureThree.state_transition_in_refl I y \<Longrightarrow>
  a \<in> actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
  (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow>
            ((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
            (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {}))) \<Longrightarrow>
  (\<forall> l \<in> nodes(InfrastructureThree.graphI I).
             \<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI I) l).
             (\<exists> a \<in> agra (InfrastructureThree.graphI I) l. 
                  e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
  efids_cur(efids_inc_ind(cgra (graphI y) a)) \<notin> 
{x. \<exists>z l. x \<in> InfrastructureThree.egra (InfrastructureThree.graphI z) l \<and>
                      I \<rightarrow>\<^sub>n* z \<and> z \<rightarrow>\<^sub>n* y \<and> l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I)}"
  using lemmaD by presburger

 (*  *)
lemma lemmaBO: "y \<rightarrow>\<^sub>n z \<Longrightarrow>  l' \<in> nodes(graphI z) \<Longrightarrow> 
(\<forall> l \<in> nodes(InfrastructureThree.graphI z').
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI z') l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI z') l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a))) \<Longrightarrow>
x \<in> egra (graphI z) l' \<Longrightarrow>
       x \<notin> egra (graphI y) l' \<Longrightarrow>
   \<exists> a \<in> actors_graph (graphI y). x = efids_cur(efids_inc_ind(cgra (graphI y) a))"
proof (frule same_actors0, frule same_nodes0,rule state_transition_in.cases, assumption)
  show "\<And>G I a l l'a I'.
       y \<rightarrow>\<^sub>n z \<Longrightarrow>
       x \<in> InfrastructureThree.egra (InfrastructureThree.graphI z) l' \<Longrightarrow>
       x \<notin> InfrastructureThree.egra (InfrastructureThree.graphI y) l' \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l'a \<in> InfrastructureThree.nodes G \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l'a (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a a l l'a (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI y).
          x =
          InfrastructureThree.efids_cur
           (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI y) a))"
    by (smt (verit, ccfv_threshold) DiffD1 InfrastructureThree.egra.simps InfrastructureThree.graphI.simps InfrastructureThree.move_graph_a_def fun_upd_other fun_upd_same insertE)
next show "\<And>G I a l I'.
       y \<rightarrow>\<^sub>n z \<Longrightarrow>
       x \<in> InfrastructureThree.egra (InfrastructureThree.graphI z) l' \<Longrightarrow>
       x \<notin> InfrastructureThree.egra (InfrastructureThree.graphI y) l' \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (a := (InfrastructureThree.kgra G a)
              (l := {(x, y). x \<in> InfrastructureThree.agra G l \<and> y \<in> InfrastructureThree.egra G l}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI y).
          x =
          InfrastructureThree.efids_cur
           (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI y) a))"
    by simp
next show "\<And>G I a l I'.
       y \<rightarrow>\<^sub>n z \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z').
          \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI z') l.
             \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI z') l.
                e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z') a) \<Longrightarrow>
       x \<in> InfrastructureThree.egra (InfrastructureThree.graphI z) l' \<Longrightarrow>
       x \<notin> InfrastructureThree.egra (InfrastructureThree.graphI y) l' \<Longrightarrow>
       InfrastructureThree.actors_graph (InfrastructureThree.graphI y) =
       InfrastructureThree.actors_graph (InfrastructureThree.graphI z) \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI y) =
       InfrastructureThree.nodes (InfrastructureThree.graphI z) \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a l (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI y).
          x =
          InfrastructureThree.efids_cur
           (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI y) a))"
    by (smt (verit, best) DiffD1 InfrastructureThree.actors_graph_def InfrastructureThree.atI_def InfrastructureThree.egra.simps InfrastructureThree.graphI.simps InfrastructureThree.put_graph_efid_def fun_upd_other fun_upd_same insertE mem_Collect_eq)
qed

lemma lemmaB[rule_format]:  
  "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
  a \<in> actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
  (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow>
            ((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
            (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {}))) \<Longrightarrow>
  (\<forall> l \<in> nodes(InfrastructureThree.graphI I).
             \<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI I) l).
             (\<exists> a \<in> agra (InfrastructureThree.graphI I) l. 
                  e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
  \<forall> l \<in> nodes(graphI I). \<forall> l' \<in> nodes(graphI I).
              x \<in> egra(graphI I) l \<longrightarrow> x \<in> egra(graphI y) l' \<longrightarrow> l = l'"
proof (erule rtrancl_induct, simp)
  show "a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
    \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
       inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<Longrightarrow>
    \<forall>a l. l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
          (\<forall>l'. a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l') \<Longrightarrow>
    \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
       \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
          a \<noteq> a' \<longrightarrow>
          range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter>
          range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')) =
          {} \<Longrightarrow>
    \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI I) l.
          \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI I) l.
             e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) \<Longrightarrow>
    \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       x \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<longrightarrow>
       (\<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
           x \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')"
    by (metis (no_types, lifting) InfrastructureThree.actors_graph_def InfrastructureThree.efids_cur_in_efids_listO disjoint_insert(2) insert_Diff mem_Collect_eq)
next show
  "\<And>y z. a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
           \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
              inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
              \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter>
                 range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')) =
                 {} \<Longrightarrow>
           \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
              \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI I) l.
                 \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI I) l.
                    e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
              \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
                 x \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<longrightarrow>
                 x \<in> InfrastructureThree.egra (InfrastructureThree.graphI y) l' \<longrightarrow> l = l' \<Longrightarrow>
           \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
              \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
                 x \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<longrightarrow>
                 x \<in> InfrastructureThree.egra (InfrastructureThree.graphI z) l' \<longrightarrow> l = l' "
    apply (rule ballI)+
    apply (rule impI)+
    apply (case_tac "x \<in> egra (graphI y) l'")
(* case x \<in> egra (graphI y) l' *)
    apply blast
(* case x \<notin> egra (graphI y) l' *)
    thm lemmaBO
    apply (subgoal_tac "\<exists>a \<in> actors_graph(graphI y). x =
    InfrastructureThree.efids_cur
     (InfrastructureThree.efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI y) a))")
    prefer 2
    apply (smt (verit, ccfv_threshold) CollectD InfrastructureThree.same_nodes case_prodD lemmaBO rtrancl.rtrancl_into_rtrancl)
    apply (erule bexE)
    apply (subgoal_tac "x \<notin> 
                  {x. (\<exists> q l. x \<in> egra (graphI q) l \<and> (InfrastructureThree.state_transition_in_refl I q) \<and> 
                       (InfrastructureThree.state_transition_in_refl q y) \<and> l \<in> nodes (graphI I))}")
     prefer 2
     apply (rotate_tac -1)
     apply (erule ssubst)
    thm InfrastructureThree.state_transition_in_refl_def
     apply (rule lemmaDO)
    using InfrastructureThree.state_transition_in_refl_def apply presburger
    using InfrastructureThree.same_actors apply presburger
        apply assumption
       apply assumption
      apply assumption
     apply assumption
    using InfrastructureThree.state_transition_in_refl_def by auto
qed

(* If two properties hold in a reachable state y, they have been "collected"  
   on previous states z z' which lie on _one_ path to y *)
(* This lemma is trivial: that is not what we want!
lemma lemmaAO: "(I, y) \<in> {(x::InfrastructureThree.infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                 P y \<and> Q y \<Longrightarrow>
                (\<exists> z z'. (I \<rightarrow>\<^sub>n* z) \<and> (I \<rightarrow>\<^sub>n* z') \<and> ((z \<rightarrow>\<^sub>n* z') \<or> (z' \<rightarrow>\<^sub>n* z))
                       \<and> (z \<rightarrow>\<^sub>n* y) \<and> (z' \<rightarrow>\<^sub>n* y) \<and> P z \<and> Q z' )"
  using InfrastructureThree.state_transition_in_refl_def by blast
*)

inductive path :: "[infrastructure, infrastructure, infrastructure list] \<Rightarrow> bool"
  where
  empty: "path I I [I]"
| step: "path z y p \<Longrightarrow>  I \<rightarrow>\<^sub>n z \<Longrightarrow> path I y (I # p)"


lemma fst_in_path: "path I y p \<Longrightarrow> I \<noteq> y \<Longrightarrow> I \<in> set p"
  by (metis list.set_intros(1) path.cases)

lemma fst_in_pathO: "path I y p \<Longrightarrow> I \<noteq> y \<Longrightarrow> I = hd p"
  by (metis list.sel(1) path.cases)

lemma fst_in_pathOO: "path I y p \<Longrightarrow> I \<in> set p"
  by (metis list.set_intros(1) path.cases)


(* lemma path_singleton: "path I y [a] \<Longrightarrow> I = y" 
letzte Element nicht im Pfad! *)


lemma lst_in_path: "\<forall> I y. path I y p \<longrightarrow> I \<noteq> y \<longrightarrow> y \<in> set p"
  apply (rule list.induct)
   apply (metis empty_iff empty_set fst_in_path)
  by (metis list.inject list.set_intros(1) list.set_intros(2) path.cases)

lemma lst_in_pathOO: "path I y p \<Longrightarrow> y \<in> set p"
  using fst_in_pathOO lst_in_path by blast



primrec before :: "['a, 'a, 'a list] \<Rightarrow> bool"
  where
before_empty: "before x y [] = False" |
before_step: "before x y (z # p) = (if x = y \<or> y = z then False
                                   else (if x = z then y \<in> set p else before x y p))"

lemma before_eq: "before x x (x # l) = False"
  by simp

lemma before_neq : "x \<noteq> y \<Longrightarrow> before x y (x # l) = (y \<in> set l)"
  by simp

lemma list_split: "x \<in> set l \<Longrightarrow> \<exists> lO lI. x \<notin> set lO \<and> hd(lI) = x \<and> lO @ lI = l"
  using split_list_first by force

lemma before_test: "before (1:: nat) (2:: nat) [1,2] = (2 \<in> set([2]))"
  by simp

lemma before_snd_not[rule_format]: "x \<noteq> y \<longrightarrow>  x \<notin> set ys \<longrightarrow> before x y (ys @ x # zs) \<longrightarrow> y \<notin> set ys"
  apply (rule_tac list = ys in list.induct)
  apply fastforce
  by simp

lemma before_neg[rule_format]: "z \<noteq> z' \<longrightarrow> z \<in> set p \<longrightarrow> z' \<in> set p \<longrightarrow> \<not> before z z' p \<longrightarrow> before z' z p"
  apply (rule_tac list = p in list.induct)
  apply force
  by simp


lemma split_list_first_before: "x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> before x y xs \<Longrightarrow>
                        \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> set ys \<and> y \<notin> set ys \<and> y \<in> set zs"
  apply (frule split_list_first)
  by (metis Un_iff before_snd_not before_step insert_iff list.set_cases list.simps(15) set_append)

lemma list_split_split: "x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> before x y xs \<Longrightarrow> 
                        \<exists> ys zs zs'. xs = ys @ (x # (zs @ (y # zs')))"
  apply (frule split_list_first_before)
  prefer 2
  apply assumption+
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule ssubst)
  apply (rule_tac x = ys in exI)
  apply simp
  by (simp add: split_list)

lemma path_imp_rtrancl: "path I y p \<Longrightarrow> (I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  apply (erule path.induct,simp)
  by (simp add: converse_rtrancl_into_rtrancl)

lemma rtrancl_imp_ex_path: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                           \<exists> p. path I y p"
proof (erule converse_rtrancl_induct)
  show " \<exists>p. path y y p"
    apply (rule_tac x = "[y]" in exI)
    by (rule path.empty)
next show "\<And>ya z. (ya, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow> (z, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> \<exists>p. path z y p \<Longrightarrow> \<exists>p. path ya y p "
   by (metis CollectD case_prodD path.step) 
qed

lemma rtrancl_imp_ex_pathO: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> I \<noteq> y \<Longrightarrow>
                           \<exists> p. path I y p \<and> 2 \<le> length p"
  by (metis list.distinct(1) list.sel(3) path.cases rtrancl_imp_ex_path tl_nempty_lngth)


lemma path_fstO:  "\<forall> I y. path I y p \<longrightarrow> I \<noteq> y \<longrightarrow> (\<exists> zs. p = I # zs)"
  using path.simps by blast

lemma path_lstO: "\<forall> I y. path I y p \<longrightarrow> p \<noteq> [] \<longrightarrow> (\<exists> zs. p = zs @ [y])"
  apply (rule_tac list = p in list.induct)
  apply (metis empty_iff empty_set lst_in_path)
  by (metis append.simps(1) append.simps(2) list.inject list.sel(1) path.cases)

lemma path_fst: "\<forall> I y. path I y p \<longrightarrow> I \<noteq> y \<longrightarrow> (\<exists> zs. p = (I # (zs @ [y])))"
  apply (rule_tac list = p in list.induct)
  apply (metis empty_iff empty_set fst_in_path)
  by (metis append_butlast_last_id fst_in_pathO last.simps list.discI list.sel(1) path_lstO snoc_eq_iff_butlast)

lemma path_fst_lst[rule_format]: "(\<forall> y. path (hd p) y p \<longrightarrow> hd p \<noteq> y \<longrightarrow> (\<exists> xs. p = (hd p #(xs @ [y]))))"
  apply (rule_tac list = p in list.induct)
   apply (metis empty_iff empty_set lst_in_path)
  apply (rule allI)+
  apply (rule impI)+
  apply simp
  apply (drule_tac x = y in spec)
  by (meson list.inject path_fst)

lemma path_splitO[rule_format]:  "\<forall> I y. path I y (ys @ (z # zs)) \<longrightarrow> path I z (ys @ [z]) \<and> path z y (z # zs)"
  apply (rule_tac list = ys in list.induct)
  apply (metis append_Nil empty list.sel(1) path.cases)
  by (smt (verit, best) append_Cons append_is_Nil_conv list.discI list.inject path.cases path.step)

lemma path_split:  "path I y p \<Longrightarrow> p = ys @ (z # (zs @ (z' # zs'))) \<Longrightarrow> 
                    path I z (ys @ [z]) \<and> path z z' (z # zs @ [z']) \<and> path z' y (z' # zs')"
  by (metis append_Cons path_splitO)


lemma lemmaFO: "path I y p \<Longrightarrow> z \<in> set p \<Longrightarrow> z' \<in> set p \<Longrightarrow> before z z' p \<Longrightarrow>
               (I, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<and>
               (z, z') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<and>
               (z', y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  apply (subgoal_tac "\<exists> ys zs zs'. p = ys @ (z # (zs @ (z' # zs')))")
   prefer 2
   apply (rule list_split_split, assumption+)
  apply (erule exE)+
  apply (frule path_split, assumption)
  apply (erule conjE)+
  apply (rule conjI, erule path_imp_rtrancl)+
  by (erule path_imp_rtrancl)

lemma lemmaFOa: "path I y p \<Longrightarrow> z \<in> set p \<Longrightarrow> 
               (I, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<and>
               (z, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (metis path_imp_rtrancl path_splitO split_list_last)

lemma lemmaFOOOO: "path I y p \<Longrightarrow>z \<in> set p \<Longrightarrow> z' \<in> set p \<Longrightarrow> (z \<rightarrow>\<^sub>n* z') \<or> (z' \<rightarrow>\<^sub>n* z)"
  apply (case_tac "z = z'")
   apply (simp add: InfrastructureThree.state_transition_in_refl_def)
(* z \<noteq> z' *)
  apply (case_tac "before z z' p")
   apply (simp add: InfrastructureThree.state_transition_in_refl_def lemmaFO)
  by (meson InfrastructureThree.state_transition_in_refl_def before_neg lemmaFO)

(* here *)

definition first 
  where \<open>first p z x a l \<equiv> (x \<in> kgra (graphI z) a l \<and> (\<exists> zO \<in> set p.  zO  \<rightarrow>\<^sub>n z \<and> x \<notin> (kgra (graphI zO) a l)))\<close>

lemma "\<not>  path z I []"
  by (meson list.distinct(1) path.cases)

(*
function list_Suc 
  where "list_Suc a l = (case l of [] \<Rightarrow> None 
                                | [_] \<Rightarrow> None 
                                | x # l \<Rightarrow> if x = a then Some(hd l)
                                           else list_Suc a (tl l))"
  apply force
  by blast
*)

fun list_Suc 
  where 
  list_Suc_empty: "list_Suc a [] = None"
| list_Suc_singleton:  "list_Suc a [_] = None"
| list_Suc_step: "list_Suc a (x # l) = (if x = a then Some(hd l) else list_Suc a (l))"

definition list_suc
  where 
    "list_suc l n = (if Suc n < (length l) then Some(nth l (Suc n)) else None)" 


lemma "length [1,2,3] = 3"
  by simp

lemma "nth [1 :: nat,2,3] 2 = 3"
  by simp


lemma "list_suc [1:: nat, 2, 3, 3] (0 :: nat) = Some 2"
  by (simp add: list_suc_def)

lemma "list_suc [1:: nat, 2, 3, 3] (1 :: nat) = Some 3"
  by (simp add: list_suc_def)

lemma "list_suc [1:: nat, 2, 3, 3] (2 :: nat) = Some 3"
  by (simp add: list_suc_def)


(*
fun list_Suc 
  where 
  list_Suc_empty: "list_Suc a [] = None"
| list_Suc_singleton:  "list_Suc a [_] = None"
| list_Suc_step: "list_Suc a (x # l) = (if x = a \<and> (hd l) \<noteq> a then Some(hd l) else list_Suc a (l))"
*)
(*
fun list_SucP 
  where 
  list_SucP_empty: "list_SucP P [] = None"
| list_SucP_singleton:  "list_SucP P [_] = None"
| list_SucP_step: "list_SucP P (x # l) = (if P x  then Some(hd l) else list_Suc a (l))"
*)

lemma list_Suc_def: "\<forall> a l. list_Suc a l = (case l of [] \<Rightarrow> None 
                                | [_] \<Rightarrow> None 
                                | x # l \<Rightarrow> if x = a then Some(hd l)
                                           else list_Suc a (l))"
  by (smt (verit, best) list.simps(4) list.simps(5) list_Suc.elims)

lemma list_Suc_test: "list_Suc (1::nat) [1,1,2] = Some 1"
  by simp

lemma list_Suc_testO: "list_Suc (1::nat) [3,2,1,2] = Some 2"
  by simp

lemma list_Suc_testOO: "list_Suc (1::nat) [2,1,1] = Some 1"
  by simp

lemma list_Suc_testO: "p = xs @ (x # ys) \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> x \<notin> set xs \<Longrightarrow> list_Suc x p = Some(hd ys)"
  oops


definition list_Pred   where "list_Pred a l = list_Suc a (rev l)"


lemma list_Pred_test: "list_Pred (2::nat) [1,1,2] = Some (1 :: nat)"
  by (simp add: list_Pred_def)


fun list_Pre 
  where 
  list_Pre_empty: "list_Pre a [] = None"
| list_Pre_singleton:  "list_Pre a [_] = None"
| list_Pre_step: "list_Pre a (x # l) = (if a = (hd l) then Some(x) else list_Pre a l)"


lemma path_list_Suc[rule_format]: "path I y p \<Longrightarrow> \<forall> z \<in> set p. z \<noteq> y \<longrightarrow> (\<exists> zO. list_Suc z p = Some zO \<longrightarrow> z \<rightarrow>\<^sub>n zO)"
  apply (erule path.induct)
  apply simp
  by (metis option.inject)

lemma path_list_SucO[rule_format]: "path I y p \<Longrightarrow> \<forall> z \<in> set p. z \<noteq> y \<longrightarrow> 
                                 (\<forall> zO. list_Suc z p = Some zO \<longrightarrow> z \<rightarrow>\<^sub>n zO)"
  apply (erule path.induct)
   apply simp
  apply (rule ballI)+
  apply (rule impI)
  apply (rule allI)
  apply (rule impI)
  by (smt (verit, del_insts) list.discI list.sel(1) list.sel(3) list_Suc.elims option.inject path.cases set_ConsD)

(* this is not always the case *)
lemma path_list_Suc_sum_not_end: "list_Suc z p = Some zO \<Longrightarrow> z \<noteq> last p"
  oops

lemma path_list_SucOO[rule_format]: "path I y p \<Longrightarrow> \<forall> z \<in> set p.
                                 (\<forall> zO. list_Suc z p = Some zO \<longrightarrow> z \<rightarrow>\<^sub>n zO)"
  apply (erule path.induct)
   apply simp
  apply (rule ballI)+
  apply (rule allI)
  apply (rule impI)
  by (smt (verit, best) list.discI list.sel(1) list.sel(3) list_Suc.elims option.inject path.cases set_ConsD)

lemma path_list_suc: "path I y p \<Longrightarrow> \<forall> n < (length p) - 1. nth p n \<rightarrow>\<^sub>n the(list_suc p n)"
  apply (erule path.induct)
   apply simp
  apply (simp add: list_suc_def)
  by (smt (verit, del_insts) One_nat_def diff_Suc_1 less_Suc_eq_0_disj less_imp_Suc_add nth_Cons' option.sel path.cases)

lemma path_list_sucOO[rule_format]: "path I y p \<Longrightarrow> \<forall> n < (length p) - 1. nth p n \<rightarrow>\<^sub>n nth p (Suc n)"
  apply (erule path.induct)
   apply simp
  by (smt (verit, best) Groups.add_ac(2) One_nat_def Suc_pred add_diff_cancel_left' less_Suc_eq_0_disj less_imp_Suc_add list.size(4) nth_Cons_0 nth_Cons_Suc path.cases zero_less_Suc)
  

lemma path_List_PreO: "path I y p \<Longrightarrow> \<forall> z \<in> set p.
                                 (list_Pre z p \<noteq>  None \<longrightarrow> the(list_Pre z p) \<rightarrow>\<^sub>n z)"
  apply (erule path.induct)
   apply simp
  apply (rule ballI)+
  apply simp
  apply (clarify)
  apply simp
  oops

lemma path_List_Pre: "path I y p \<Longrightarrow> \<forall> z \<in> (set p - {I}).
                                 (\<forall> zO. list_Pre z p = Some zO \<longrightarrow> zO \<rightarrow>\<^sub>n z)"
  apply (erule path.induct)
   apply simp
  apply (rule ballI)+
  apply (rule allI)
  thm list_Pre_step
(* list_Pre ?a (?x # ?v # ?va) = (if ?a = hd (?v # ?va) then Some ?x else list_Pre ?a (?v # ?va)) *)
  apply (rule impI)
  apply (case_tac p)
   apply simp
  apply simp
  by (metis insert_Diff insert_iff list.inject option.inject path.cases)

(* Not true: you may have a list that starts with two I's *)
lemma path_List_PreI: "path I y p \<Longrightarrow> list_Pre I p = None"
  apply (erule path.induct)
   apply simp
  oops



(* See conterexample: if there are repititions, then the reverse gets the wrong end *)
lemma List_Pred_Suc: "list_Pred z p = Some zO \<Longrightarrow> list_Suc zO p = Some z"
  oops

lemma pred_prestate: "path I y p \<Longrightarrow> \<forall> z \<in> set p.
                      \<forall> zO. list_Pred z p = Some zO \<longrightarrow> zO \<rightarrow>\<^sub>n z"
  apply (unfold list_Pred_def)
  apply (erule path.induct)
   apply simp
  apply (rule ballI)+
  apply (rule allI)
  apply (rule impI)

  apply (simp add: list_Pred_def)
  apply (frule path_list_Suc)
  prefer 2
  oops

(* Not valid as we could have repetitions in paths: if we exclude
  them, we lose that for server I \<rightarrow>* y there is a path (see lemma rtrancl_imp_ex_path) *)
lemma "path I I p \<Longrightarrow> p = [I]"
  apply (erule path.cases)
   apply simp+
  oops


(* not valid because there could be repetitions in p 
lemma lemma_pathOOO: "\<forall> y . path y y p \<longrightarrow> p = [y]"
  apply (rule_tac list = p in list.induct)
   apply (meson list.distinct(1) path.cases)

  apply (meson list.distinct(1) path.cases)
   
  apply (rule path.cases, assumption, simp)


  oops
*)

  thm path.induct

fun flt
  where 
    flt_empty: "flt P [] = None"
  | flt_step: "flt P (a # l) = (if P a then Some a else flt P l)"

lemma P_notP_nthlist[rule_format]: "2 \<le> length p \<longrightarrow> \<not> P (nth p 0) \<longrightarrow> P (nth p (length p - 1)) \<longrightarrow>
     (\<exists> n < length p - 1. \<not> P (nth p n) \<and> P(nth p (Suc n)))"
  apply (rule list.induct)
  apply simp
  by (metis (no_types, hide_lams) One_nat_def Suc_1 Suc_diff_1 Suc_le_mono Suc_less_eq diff_Suc_1 le0 length_Cons nth_Cons' nth_non_equal_first_eq zero_less_Suc)


lemma P_notP_list: "(P y) \<longrightarrow> \<not> (P I) \<longrightarrow> 
         (\<exists> zO \<in> set (I # (q @ [y])). \<not> P zO \<and> P(the(list_Suc zO (I # (q @ [y])))))"

(* new:
Auto Quickcheck found a counterexample:
  P = {a\<^sub>1}
  y = a\<^sub>1
  I = a\<^sub>2
  q = [a\<^sub>3, a\<^sub>2]

old counterexample:
 P = {a\<^sub>1}
  y = a\<^sub>1
  I = a\<^sub>2
  q = [a\<^sub>2]
p = [a2,a2,a1] 
that is: \<not> P I = I \<notin> {a1} because I = a2 and \<not> P z forall z \<in> q, because q = [a2], and P y because y = a1 \<in> {a1} = P
so, why?
*)
  oops

lemma P_notP_list: "(P y) \<longrightarrow> \<not> (P I) \<longrightarrow>
         (\<exists> zO \<in> set (I # ([x]@ [y])). \<not> P zO \<and> P(the(list_Suc zO (I # ([x] @ [y])))))"
(* 
Auto Quickcheck found a counterexample:
  P = {a\<^sub>1}
  y = a\<^sub>1
  I = a\<^sub>2
  x = a\<^sub>2
*)
  apply (rule impI)+
  apply (case_tac "P x")
   apply simp
  apply (case_tac "I = x")
  apply (rule_tac x = x in bexI)
   apply (rule conjI, assumption)
   apply simp
(*  1. P y \<Longrightarrow> \<not> P I \<Longrightarrow> \<not> P x \<Longrightarrow> I \<noteq> x
 Oh, we don't know whether the elements are different, so list_Suc cannot be decided 
- we probably need a list_Suc with a different property than = .
Also adding path to it doesn't change much
 path I y (I # ([x]@ [y])) \<longrightarrow>
counterexample isn't found but still the same subgoal to show I \<noteq> x
*)
   apply (subgoal_tac "list_Suc x (I # [x] @ [y]) = Some y")
  prefer 2
  apply (rule list.induct)
  oops

lemma nth_p_y: "path I y p \<Longrightarrow> y = nth p (length p - 1)"
  by (metis empty_iff empty_set fst_in_pathOO length_last path_lstO)


lemma lemmaFOOb: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                 (\<forall> l a. kgra (graphI I) a l = {}) \<Longrightarrow>
                  a \<in> actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
                 x \<in> kgra (graphI y) a l \<Longrightarrow>
                 \<forall> p. path I y p \<longrightarrow> (\<exists> z \<in> set p. first p z x a l)"
  apply (rule allI)
  apply (rule impI)
  apply (unfold first_def)
  apply (subgoal_tac "x \<notin> kgra (graphI I) a l")
   prefer 2
   apply blast
  apply (subgoal_tac "I \<noteq> y")
  prefer 2
   apply blast
  apply (subgoal_tac "2 \<le> length p")
  prefer 2
   apply (metis list.discI list.sel(3) path.cases tl_nempty_lngth)
  apply (subgoal_tac "I = nth p 0")
  prefer 2
   apply (metis nth_Cons_0 path.cases)
  apply (subgoal_tac "y = nth p (length p - 1)")
   prefer 2
  using nth_p_y apply presburger
  apply (subgoal_tac 
     "(\<exists> n < length p - 1. \<not> (x \<in> kgra (graphI (nth p n)) a l)  \<and> x \<in> kgra (graphI (nth p (Suc n))) a l)")
   prefer 2
   apply (rule P_notP_nthlist, assumption+, simp, simp)
  apply (erule exE)
  apply (erule conjE)+
  apply (rule_tac x = "p ! Suc n" in bexI)
  apply (rule conjI, assumption)
  apply (rule_tac x = "p ! n" in bexI)
    apply (rule conjI)
     apply (erule path_list_sucOO, assumption)
    apply assumption
   by simp+

(* here - hurrah !*)

lemma lemmaFOOO: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                   a \<in> actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
                   x \<in> kgra (graphI y) a l \<Longrightarrow>  path I y p \<Longrightarrow>
                   z \<in> set p \<Longrightarrow> first p z x a l \<Longrightarrow> snd x \<in> egra (graphI z) l"
  apply (simp add: first_def)
  apply (erule conjE)
  apply (erule bexE)
  apply (erule conjE)
  apply (rule state_transition_in.cases, assumption)
  apply (metis InfrastructureThree.graphI.simps InfrastructureThree.kgra.simps InfrastructureThree.move_graph_a_def)
  apply (metis (no_types, lifting) CollectD InfrastructureThree.egra.simps InfrastructureThree.graphI.simps InfrastructureThree.kgra.simps case_prodE fun_upd_other fun_upd_same snd_conv)
  by (simp add: InfrastructureThree.put_graph_efid_def)

lemma lemmaF[rule_format]:  "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                 (\<forall> l a. kgra (graphI I) a l = {}) \<Longrightarrow>
                  a \<in> actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
                 x \<in> kgra (graphI y) a l \<Longrightarrow>
                 \<forall> p. path I y p \<longrightarrow> (\<exists> z \<in> set p. snd x \<in> egra (graphI z) l)"
  by (meson lemmaFOOb lemmaFOOO)

(* Theorem A funktioniert, wenn FOO und FOOO gezeigt werden koennen -- was wir nun konnten! *)
theorem theoremA: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
         (\<forall> l a. kgra (graphI I) a l = {}) \<Longrightarrow>
         a \<in> actors_graph (graphI I) \<Longrightarrow> 
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
  (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow>
            ((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
            (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {}))) \<Longrightarrow>
  (\<forall> l \<in> nodes(InfrastructureThree.graphI I).
             \<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI I) l).
             (\<exists> a \<in> agra (InfrastructureThree.graphI I) l. 
                  e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
  \<forall> l \<in> nodes(graphI I). \<forall> l' \<in> nodes(graphI I).
         x \<in> kgra (graphI y) a l \<inter> kgra (graphI y) a l' \<longrightarrow> l = l'" 
  apply (rule ballI)+
  apply (rule impI)
  apply simp
  apply (erule conjE)+
(* intervention to show that I \<noteq> y might enable to show that there is a path p with at least two elements*)
  apply (subgoal_tac "I \<noteq> y")
  prefer 2
   apply blast
  apply (subgoal_tac "\<exists> p. path I y p")
  prefer 2
  apply (erule rtrancl_imp_ex_path)
  apply (erule exE)
  apply (subgoal_tac "(\<exists> z \<in> set p. snd x \<in> egra (graphI z) l)")
   apply (subgoal_tac "(\<exists> z \<in> set p. snd x \<in> egra (graphI z) l')")
    prefer 2
  using lemmaF apply presburger 
   prefer 2
  using lemmaF apply presburger
  apply (erule bexE)+
  apply (case_tac "before z za p")
  apply (frule_tac z = z and z' = za in lemmaFO, assumption+)
  apply (erule conjE)+
   apply (rule_tac x = "snd x" and I = z and y = za and a = a in lemmaB)
  apply assumption
  apply (metis InfrastructureThree.same_actors)
  apply (metis InfrastructureThree.same_actors efids_list_eq_refl)
  using InfrastructureThree.actor_unique_loc_lem apply presburger
  apply (metis InfrastructureThree.same_actors efids_list_eq_refl)
  using InfrastructureThree.efids_cur_eq_egra_refl apply auto[1]
  apply (metis InfrastructureThree.same_nodes)
     apply (metis InfrastructureThree.same_nodes)
    apply assumption+
(* z = za *)
  apply (case_tac "z = za")
  apply (frule_tac z = z in lemmaFOa, assumption+)
  apply (erule conjE)+
   apply (rule_tac x = "snd x" and I = za and y = za and a = a in lemmaB)
            apply simp
  apply (metis InfrastructureThree.same_actors)
  apply (metis InfrastructureThree.same_actors efids_list_eq_refl)
  using InfrastructureThree.actor_unique_loc_lem apply presburger
  apply (metis InfrastructureThree.same_actors efids_list_eq_refl)
  using InfrastructureThree.efids_cur_eq_egra_refl apply auto[1]
  apply (metis InfrastructureThree.same_nodes)
     apply (metis InfrastructureThree.same_nodes)
    apply simp
  apply assumption
(* z \<noteq> za and \<not> before z za p*)
  apply (frule_tac z = za and z' = z in lemmaFO, assumption+)
  apply (simp add: before_neg)
  apply (erule conjE)+
  apply (rule sym)
   apply (rule_tac x = "snd x" and I = za and y = z and a = a in lemmaB)
  apply assumption
  apply (metis InfrastructureThree.same_actors)
  apply (metis InfrastructureThree.same_actors efids_list_eq_refl)
  using InfrastructureThree.actor_unique_loc_lem apply presburger
  apply (metis InfrastructureThree.same_actors efids_list_eq_refl)
  using InfrastructureThree.efids_cur_eq_egra_refl apply auto[1]
  apply (metis InfrastructureThree.same_nodes)
     apply (metis InfrastructureThree.same_nodes)
  by assumption+

(* here -- finally *)
lemma theoremAOO: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
         (\<forall> l a. kgra (graphI I) a l = {}) \<Longrightarrow>
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
  (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
  (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow>
            ((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
            (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {}))) \<Longrightarrow>
  (\<forall> l \<in> nodes(InfrastructureThree.graphI I).
             \<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI I) l).
             (\<exists> a \<in> agra (InfrastructureThree.graphI I) l. 
                  e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
\<forall> a \<in> actors_graph (graphI y). 
  \<forall> l \<in> nodes(graphI y). \<forall> l' \<in> nodes(graphI y). l \<noteq> l'
       \<longrightarrow>  kgra (graphI y) a l \<inter> kgra (graphI y) a l' = {}"
  by (smt (verit) InfrastructureThree.same_actors InfrastructureThree.same_nodes empty_Collect_eq inf_set_def mem_Collect_eq theoremA)

(* Single-set intersection lemma is given by invariant that there are more than 3 - ergo not identifiable *)
(*
lemma  "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureThree.graphI I).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI I) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI I) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
\<forall> l \<in> nodes(InfrastructureThree.graphI y).
 \<forall>x\<in>InfrastructureThree.agra (InfrastructureThree.graphI y) l.
       InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) x)
       \<in> InfrastructureThree.egra (InfrastructureThree.graphI y) l"
  apply (subgoal_tac "(\<forall> l \<in> nodes(InfrastructureThree.graphI y).
\<forall> e \<in> (InfrastructureThree.egra (InfrastructureThree.graphI y) l).
 (\<exists> a \<in> agra (InfrastructureThree.graphI y) l. 
     e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)))")
  apply (subgoal_tac "(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI y) \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI y) l \<longrightarrow>  
                a \<in>  InfrastructureThree.agra (InfrastructureThree.graphI y) l' \<longrightarrow> l = l'))")
  prefer 2
  using InfrastructureThree.actor_unique_loc_lem apply presburger
  prefer 2
   apply (simp add: InfrastructureThree.efids_cur_eq_egra_refl)
  apply (rule ballI)+
  apply (rotate_tac -4)
  apply (drule_tac x = l in bspec)
   apply assumption
  apply (rotate_tac -1)
  apply (drule_tac x = "efids_cur (cgra (InfrastructureThree.graphI y) x)" in bspec)
produces "InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) x)
           \<in> InfrastructureThree.egra (InfrastructureThree.graphI y) l " which is the goal as
  subgoal 
*)
lemma isthere_lem0: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
           (inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI z) x)) 
                     (actors_graph (InfrastructureThree.graphI z))) \<longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
      efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureThree.cgra (graphI z) a)) \<in> egra (graphI z) l)) 
        \<longrightarrow> (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  a \<in>  agra (graphI z') l' \<longrightarrow>
          efids_cur ((InfrastructureThree.cgra (graphI z') a)) \<in> egra (graphI z') l'))"
  apply (rule allI)+
  apply (rule impI)
  apply (rule InfrastructureThree.state_transition_in.cases, assumption)
    apply (simp add: move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
     apply (rule allI)
     apply (rule conjI)
     apply (rule impI)+
     apply (rule allI)
     apply (rule impI)+
      apply (erule conjE)+
  apply meson
  apply (metis (no_types, lifting) InfrastructureThree.actors_graph_def inj_on_def mem_Collect_eq)
  apply force
(* get *)
  using InfrastructureThree.agra.simps InfrastructureThree.cgra.simps InfrastructureThree.egra.simps InfrastructureThree.graphI.simps apply presburger
(* put *)
  by (smt (z3) InfrastructureThree.actors_graph_def InfrastructureThree.agra.simps InfrastructureThree.atI_def InfrastructureThree.cgra.simps InfrastructureThree.egra.simps InfrastructureThree.graphI.simps InfrastructureThree.put_graph_efid_def fun_upd_apply inj_on_def insert_Diff insert_iff mem_Collect_eq)

lemma isthere_lem0a: "z \<rightarrow>\<^sub>n z' \<Longrightarrow>  nodes (graphI z) = nodes (graphI z') \<Longrightarrow>
           (inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI z) x)) 
                     (actors_graph (InfrastructureThree.graphI z))) \<Longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
      efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<Longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureThree.cgra (graphI z) a)) \<in> egra (graphI z) l)) \<Longrightarrow>
         (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  a \<in>  agra (graphI z') l' \<longrightarrow>
          efids_cur ((InfrastructureThree.cgra (graphI z') a)) \<in> egra (graphI z') l'))"
  using InfrastructureThree.isthere_lem0 by presburger

lemma isthere_lem00: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
           (inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI z) x)) 
                     (actors_graph (InfrastructureThree.graphI z))) \<longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
      inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureThree.cgra (graphI z) a)) \<in> egra (graphI z) l)) 
        \<longrightarrow> (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  a \<in>  agra (graphI z') l' \<longrightarrow>
          efids_cur ((InfrastructureThree.cgra (graphI z') a)) \<in> egra (graphI z') l'))"
  by (simp add: InfrastructureThree.efids_list_inj_imp_inc_ind_not_eq InfrastructureThree.isthere_lem0)

lemma isthere_lem00a: "z \<rightarrow>\<^sub>n z' \<Longrightarrow> nodes (graphI z) = nodes (graphI z') \<Longrightarrow>
           (inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI z) x)) 
                     (actors_graph (InfrastructureThree.graphI z))) \<Longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
      inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<Longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureThree.cgra (graphI z) a)) \<in> egra (graphI z) l)) \<Longrightarrow>
         (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  a \<in>  agra (graphI z') l' \<longrightarrow>
          efids_cur ((InfrastructureThree.cgra (graphI z') a)) \<in> egra (graphI z') l'))"
  using InfrastructureThree.isthere_lem00 by presburger

lemma is_there_lem[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
     (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
      (range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')))) = {}))) \<Longrightarrow>
        (inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI I) x)) 
                     (actors_graph (InfrastructureThree.graphI I))) \<Longrightarrow>
        (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
           (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>
                a \<in>  agra (graphI I) l \<longrightarrow>  a \<in>  agra (graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> a.
             (\<forall> l. l \<in> nodes (graphI I) \<longrightarrow>  a \<in>  agra (graphI I) l \<longrightarrow>
            efids_cur ((InfrastructureThree.cgra (graphI I) a)) \<in> egra (graphI I) l)) \<longrightarrow>
        (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI y) \<longrightarrow>  a \<in>  agra (graphI y) l' \<longrightarrow>
                  efids_cur ((InfrastructureThree.cgra (graphI y) a)) \<in> egra (graphI y) l'))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
              \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter>
                 range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')) =
                 {} \<Longrightarrow>
           inj_on (\<lambda>x. InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) x))
            (InfrastructureThree.actors_graph (InfrastructureThree.graphI I)) \<Longrightarrow>
           \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
              inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
              a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           (\<forall>a l. l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
                  a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
                  InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)
                  \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l) \<longrightarrow>
           (\<forall>a l'.
               l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI y) \<longrightarrow>
               a \<in> InfrastructureThree.agra (InfrastructureThree.graphI y) l' \<longrightarrow>
               InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI y) a)
               \<in> InfrastructureThree.egra (InfrastructureThree.graphI y) l') \<Longrightarrow>
           (\<forall>a l. l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
                  a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
                  InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)
                  \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l) \<longrightarrow>
           (\<forall>a l'.
               l' \<in> InfrastructureThree.nodes (InfrastructureThree.graphI z) \<longrightarrow>
               a \<in> InfrastructureThree.agra (InfrastructureThree.graphI z) l' \<longrightarrow>
               InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)
               \<in> InfrastructureThree.egra (InfrastructureThree.graphI z) l')"
    apply (rule impI)
  apply (rule_tac z = y in isthere_lem00a)
    apply force
    apply (metis InfrastructureThree.same_nodes rtrancl.rtrancl_into_rtrancl)
    apply (smt (verit, ccfv_threshold) InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.same_actors disjoint_insert(2) efids_list_eq_refl inj_onI insert_Diff)
    apply (metis InfrastructureThree.same_actors efids_list_eq_refl)
    using InfrastructureThree.actor_unique_loc_lem apply presburger
    by meson
qed



lemma inj_on_leq: "inj_on f A \<Longrightarrow>
    AO \<subseteq> A \<Longrightarrow> \<forall> x \<in> AO. f x \<in> EO \<Longrightarrow> finite EO \<Longrightarrow>
    3 \<le> card AO \<Longrightarrow>
    3 \<le> card EO"
  apply (subgoal_tac "card AO \<le> card EO")
   apply (meson dual_order.trans)
  apply (rule_tac f = f in card_inj_on_le)
  using inj_on_subset apply blast
  apply fastforce
  using card_ge_0_finite by blast

lemma finite_egras_inv: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> (\<forall> l \<in> nodes (graphI z). finite(egra (graphI z) l)) 
                         \<longrightarrow> (\<forall> l' \<in> nodes (graphI z'). finite(egra (graphI z') l'))"
  apply (rule allI)+
  apply (rule impI)
  apply (rule InfrastructureThree.state_transition_in.cases, assumption)
    apply (simp add: move_graph_a_def)
  apply (simp add: InfrastructureThree.same_nodes0)
  apply (simp add: InfrastructureThree.same_nodes0)
  apply (simp add: put_graph_efid_def)
  by (simp add: InfrastructureThree.same_nodes0)

lemma finite_egras_inv_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                     (\<forall> l \<in> nodes (graphI I). finite(egra (graphI I) l)) \<Longrightarrow>
                     (\<forall> l' \<in> nodes (graphI y). finite(egra (graphI y) l'))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
              finite (InfrastructureThree.egra (InfrastructureThree.graphI I) l) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI y).
              finite (InfrastructureThree.egra (InfrastructureThree.graphI y) l') \<Longrightarrow>
           \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
              finite (InfrastructureThree.egra (InfrastructureThree.graphI z) l') "
    by (simp add: finite_egras_inv)
qed

lemma finite_agras_inv: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> (\<forall> l \<in> nodes (graphI z). finite(agra (graphI z) l)) 
                         \<longrightarrow> (\<forall> l' \<in> nodes (graphI z'). finite(agra (graphI z') l'))"
  apply (rule allI)+
  apply (rule impI)
  apply (rule InfrastructureThree.state_transition_in.cases, assumption)
    apply (simp add: move_graph_a_def)
  using InfrastructureThree.nodes_def apply force
  apply (simp add: InfrastructureThree.same_nodes0)
  apply (simp add: put_graph_efid_def)
  by (simp add: InfrastructureThree.same_nodes0)

lemma finite_agras_inv_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                     (\<forall> l \<in> nodes (graphI I). finite(agra (graphI I) l)) \<Longrightarrow>
                     (\<forall> l' \<in> nodes (graphI y). finite(agra (graphI y) l'))"
proof (erule rtrancl_induct, simp)
  show " \<And>y z. \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
              finite (InfrastructureThree.agra (InfrastructureThree.graphI I) l) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI y).
              finite (InfrastructureThree.agra (InfrastructureThree.graphI y) l') \<Longrightarrow>
           \<forall>l'\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
              finite (InfrastructureThree.agra (InfrastructureThree.graphI z) l')"
    using finite_agras_inv by force
qed

lemma numbers_egras_inv: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow> 
(range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a'))) = {})) 
\<Longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI I) x)) 
           (actors_graph (InfrastructureThree.graphI I))) \<Longrightarrow>
        (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
           (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>
                a \<in>  agra (graphI I) l \<longrightarrow>  a \<in>  agra (graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> a.
             (\<forall> l. l \<in> nodes (graphI I) \<longrightarrow>  a \<in>  agra (graphI I) l \<longrightarrow>
            efids_cur ((InfrastructureThree.cgra (graphI I) a)) \<in> egra (graphI I) l)) \<Longrightarrow>
\<forall> l \<in> nodes (graphI I). finite(egra (graphI I) l) \<Longrightarrow>
 l \<in> nodes (graphI I) \<Longrightarrow> 
card (agra (graphI I) l) \<ge> 3 \<Longrightarrow>
card (egra (graphI y) l) \<ge> 3"
  apply (subgoal_tac "(inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI y) x)) 
           (actors_graph (InfrastructureThree.graphI y)))")
  prefer 2
  apply (smt (verit, ccfv_SIG) InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.ran_efids_list_disjoint_refl disjoint_iff inj_on_def)
  apply (subgoal_tac " 3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI y) l)")
   prefer 2
  using numbers_actors_inv_refl apply presburger
  apply (rule_tac A = "actors_graph (InfrastructureThree.graphI y)" and 
                  AO = "agra (InfrastructureThree.graphI y) l" and 
                  EO = "egra (InfrastructureThree.graphI y) l" in inj_on_leq)
 apply assumption
  apply (metis (mono_tags, lifting) InfrastructureThree.actors_graph_def InfrastructureThree.same_actors InfrastructureThree.same_nodes mem_Collect_eq subsetI)
    prefer 3
    apply assumption
  using InfrastructureThree.is_there_lem InfrastructureThree.same_nodes apply auto[1]
  by (metis InfrastructureThree.same_nodes finite_egras_inv_refl)

lemma two_noteq_card_ge_two: "finite A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> 2 \<le> card A"
  by (metis Suc_leI card_Diff1_less_iff card_gt_0_iff ex_in_conv finite_insert insert_Diff insert_iff less_not_le linorder_neqE_nat numeral_2_eq_2) 

lemma one_ge_card_imp_one_neq: "finite S \<Longrightarrow> 1 \<le> card S \<Longrightarrow>
       \<exists> A.  A \<in> S"
  by (metis One_nat_def Suc_le_lessD all_not_in_conv card.empty less_not_refl3)

lemma two_ge_card_imp_two_neq: "finite S \<Longrightarrow> 2 \<le> card S \<Longrightarrow>
       \<exists> A B. A \<noteq> B  \<and> A \<in> S \<and> B \<in> S"
  by (meson card_2_iff' in_mono obtain_subset_with_card_n)

lemma three_ge_card_imp_three_neqO: "finite S \<Longrightarrow> 3 \<le> card S \<Longrightarrow>
       \<exists> A B E. A \<noteq> B \<and> A \<noteq> E \<and> B \<noteq> E \<and> A \<in> S \<and> B \<in> S \<and> E \<in> S"
  by (metis Suc_le_lessD card_2_iff' less_imp_le_nat less_not_le numeral_2_eq_2 numeral_3_eq_3 two_ge_card_imp_two_neq)

lemma three_ge_card_imp_three_neq: "finite S \<Longrightarrow> 3 \<le> card S \<Longrightarrow>
       \<exists> A B E. A \<noteq> B \<and> A \<noteq> E \<and> B \<noteq> E \<and> A \<in> S \<and> B \<in> S"
  using three_ge_card_imp_three_neqO by fastforce

lemma three_ge_card_imp_two_neq_Eve: "finite S \<Longrightarrow> 3 \<le> card S \<Longrightarrow>
       \<exists>A B. A \<noteq> B \<and> A \<noteq> ''Eve'' \<and> B \<noteq> ''Eve'' \<and> A \<in> S \<and> B \<in> S"
  by (smt (verit, ccfv_SIG) card_2_iff' dual_order.antisym numeral_eq_iff obtain_subset_with_card_n order_refl semiring_norm(89) three_ge_card_imp_three_neq two_noteq_card_ge_two)

lemma last_lemOOO[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
(range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a'))) = {})) \<longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI z) x)) 
           (actors_graph (InfrastructureThree.graphI z))) \<longrightarrow>
        (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<longrightarrow>
           (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
(\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureThree.cgra (graphI z) a)) \<in> egra (graphI z) l)) \<longrightarrow>
(\<forall> l \<in> nodes (graphI z). finite(egra (graphI z) l)) \<longrightarrow>
(\<forall> l \<in> nodes (graphI z). finite(agra (graphI z) l)) \<longrightarrow>
(\<forall> l \<in> nodes (graphI z). card (agra (graphI z) l) \<ge> 3) \<longrightarrow>
(\<forall> l \<in> nodes (graphI z). card (egra (graphI z) l) \<ge> 3) \<longrightarrow>
 (\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
  {(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI z) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} \<noteq> {}
   \<longrightarrow>  2 \<le> card {(Id, Eid).
       (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI z) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid})
\<longrightarrow>  (\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z').
  {(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI z') ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} \<noteq> {}
   \<longrightarrow>  2 \<le> card {(Id, Eid).
       (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI z') ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid})"
  apply (rule allI)+
  apply (rule impI)
  apply (rule InfrastructureThree.state_transition_in.cases, assumption)
    apply (simp add: move_graph_a_def)
  using InfrastructureThree.gra.simps InfrastructureThree.nodes_def apply presburger
   prefer 2
  apply (simp add: put_graph_efid_def)
  using InfrastructureThree.graphI.simps InfrastructureThree.same_nodes0 apply presburger
  apply (rule impI)+
  apply (rule ballI)
  apply (rule impI)
(* *)
  apply simp
  apply (erule exE)
  apply (erule conjE)
(*
  apply (subgoal_tac "(\<forall> l \<in> nodes (graphI z'). card (agra (graphI z') l) \<ge> 3)
                   \<and> (\<forall> l \<in> nodes (graphI z'). card (egra (graphI z') l) \<ge> 3)")
   prefer 2
   apply (rule conjI)
  using InfrastructureThree.same_nodes0 apply force
   apply (rule ballI)
   apply (rule_tac I = z in numbers_egras_inv, force)
          apply simp+
  using InfrastructureThree.graphI.simps InfrastructureThree.same_nodes0 apply presburger
   apply (metis InfrastructureThree.same_nodes0)
*)
  apply (rule conjI)
   apply (rule impI)+
   apply (rule conjI)
    apply (rule impI)+
    defer
    apply fastforce
   apply (rule impI)+
  apply (rule conjI)
  using InfrastructureThree.same_nodes0 apply force
  using InfrastructureThree.same_nodes0 apply force
  apply simp
  apply (erule conjE)
  (*   aa \<noteq> a \<Longrightarrow>
       la = l \<Longrightarrow>
       ''Eve'' = a \<Longrightarrow>
       aa \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<Longrightarrow>
       eid \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<Longrightarrow>
       2 \<le> card {(Id, Eid).
                  Id \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<and>
                  Eid \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<and> Id \<noteq> a \<and> Eid = eid} *)
  apply (subgoal_tac "3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI I) l)")
   prefer 2
   apply fastforce
(*
  apply (subgoal_tac "3 \<le> card(InfrastructureThree.egra (InfrastructureThree.graphI I) l)")
  prefer 2
  apply fastforce
*)
  apply (subgoal_tac "? A B. A \<noteq> B \<and> A \<noteq> ''Eve'' \<and> B \<noteq> ''Eve'' \<and> A \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l
                         \<and> B \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l")
(*
   apply (subgoal_tac "? id od ad. id \<noteq> od \<and> od \<noteq> ad \<and> id \<noteq> ad \<and> {id, od, ad} \<subseteq> InfrastructureThree.egra (InfrastructureThree.graphI I) l")
*)
    apply (erule exE)+
  apply (erule conjE)+
  apply (subgoal_tac "(A, eid) \<in> {(Id, Eid).
                  Id \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<and>
                  Eid \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<and> Id \<noteq> a \<and> Eid = eid}")
  prefer 2
  apply force
  apply (subgoal_tac "(B, eid) \<in> {(Id, Eid).
                  Id \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<and>
                  Eid \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<and> Id \<noteq> a \<and> Eid = eid}")
    prefer 2
    apply force
   apply (subgoal_tac "(A,eid) \<noteq> (B, eid)")
  prefer 2
    apply blast
  apply (subgoal_tac "finite({(Id, Eid).
                  Id \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<and>
                  Eid \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<and> Id \<noteq> a \<and> Eid = eid})")
    apply (rule two_noteq_card_ge_two, assumption)
      prefer 3
  apply assumption+
      defer
  apply (subgoal_tac "finite(InfrastructureThree.agra (InfrastructureThree.graphI I) l)")
  using three_ge_card_imp_two_neq_Eve apply presburger
   apply fastforce
  apply (subgoal_tac "{(Id, Eid).
         Id \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<and>
         Eid \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<and> Id \<noteq> a \<and> Eid = eid} \<subseteq>
        {(Id, Eid).
         Id \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<and>
         Eid \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l}")
   apply (erule finite_subset)
   apply (simp add: finite_cartesian_product_iff)
  by force

lemma last_lemOOOa: "z \<rightarrow>\<^sub>n z' \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI z). a \<noteq> a' \<longrightarrow> 
(range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a)) \<inter> 
 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a'))) = {})) \<Longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI z) x)) 
           (actors_graph (InfrastructureThree.graphI z))) \<Longrightarrow>
        (\<forall> a \<in> actors_graph (InfrastructureThree.graphI z). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI z) a))) \<Longrightarrow>
           (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureThree.cgra (graphI z) a)) \<in> egra (graphI z) l)) \<Longrightarrow>
(\<forall> l \<in> nodes (graphI z). finite(egra (graphI z) l)) \<Longrightarrow>
(\<forall> l \<in> nodes (graphI z). finite(agra (graphI z) l)) \<Longrightarrow>
(\<forall> l \<in> nodes (graphI z). card (agra (graphI z) l) \<ge> 3) \<Longrightarrow>
(\<forall> l \<in> nodes (graphI z). card (egra (graphI z) l) \<ge> 3) \<Longrightarrow>
 (\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z).
  {(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI z) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} \<noteq> {}
   \<longrightarrow>  2 \<le> card {(Id, Eid).
       (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI z) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid})
\<Longrightarrow>  (\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI z').
  {(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI z') ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} \<noteq> {}
   \<longrightarrow>  2 \<le> card {(Id, Eid).
       (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI z') ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid})"
  apply (rule ballI)
  apply (rule impI)
  apply (rule last_lemOOO)
              apply assumption
  by simp+

lemma last_lemOO: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
  (\<forall> l a. kgra (graphI I) a l = {}) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureThree.graphI I). a \<noteq> a' \<longrightarrow> 
(range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter> 
 range (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a'))) = {})) 
\<Longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureThree.cgra (InfrastructureThree.graphI I) x)) 
           (actors_graph (InfrastructureThree.graphI I))) \<Longrightarrow>
        (\<forall> a \<in> actors_graph (InfrastructureThree.graphI I). 
               inj (efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a))) \<Longrightarrow>
           (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>
                a \<in>  agra (graphI I) l \<longrightarrow>  a \<in>  agra (graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> a.
             (\<forall> l. l \<in> nodes (graphI I) \<longrightarrow>  a \<in>  agra (graphI I) l \<longrightarrow>
            efids_cur ((InfrastructureThree.cgra (graphI I) a)) \<in> egra (graphI I) l)) \<Longrightarrow>
\<forall> l \<in> nodes (graphI I). finite(egra (graphI I) l) \<Longrightarrow>
(\<forall> l \<in> nodes (graphI I). finite(agra (graphI I) l)) \<Longrightarrow>
\<forall> l \<in> nodes (graphI I). card (agra (graphI I) l) \<ge> 3 \<Longrightarrow>
\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI y).
       {(Id, Eid).
        (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI y) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} \<noteq>
       {} \<longrightarrow>
       2 \<le> card {(Id, Eid).
                  (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI y) ''Eve'' l \<and>
                  Id \<noteq> ''Eve'' \<and> Eid = eid}"
  apply (erule rtrancl_induct, simp)
  apply (rule last_lemOOOa)
  apply simp
  using InfrastructureThree.ran_efids_list_disjoint_refl apply presburger
  apply (smt (z3) InfrastructureThree.efids_cur_in_efids_listO InfrastructureThree.same_actors efids_list_eq_refl inj_onI insert_Diff insert_disjoint(2))
  apply (metis InfrastructureThree.same_actors efids_list_eq_refl)
  using InfrastructureThree.actor_unique_loc_lem apply presburger
  using InfrastructureThree.is_there_lem apply auto[1]
  using finite_egras_inv_refl apply presburger
  using finite_agras_inv_refl apply presburger
  apply (simp add: InfrastructureThree.same_nodes numbers_actors_inv_refl)
  using InfrastructureThree.same_nodes inj_on_cong numbers_egras_inv apply auto[1]
  by assumption


end

 