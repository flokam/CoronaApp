theory InfrastructureTwo
  imports CoronaAppOne
begin

text \<open>The datatype stays the same in the second refinement .\<close>
(* datatype efidlist = Efids "efid" "nat" "nat \<Rightarrow> efid"  *)

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
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then 
                     ((agra g)(l := (agra g l) - {n}))(l' := (insert n (agra g l')))
                     else (agra g))
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then 
                            (cgra g)(n := efids_inc_ind(cgra g n))
                      else (cgra g))
                                 (lgra g)
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then
                       ((egra g)(l := (egra g l) - {efids_cur(cgra g n)}))
                                (l' := insert (efids_cur(efids_inc_ind(cgra g n)))(egra g l'))
                      else egra g)(kgra g)"

definition put_graph_efid :: "[identity, location, igraph] \<Rightarrow> igraph"
  where \<open>put_graph_efid n l g  \<equiv> Lgraph (gra g)(agra g)
                            ((cgra g)(n := efids_inc_ind(cgra g n)))
                               (lgra g)
                             ((egra g)(l :=  insert (efids_cur(efids_inc_ind(cgra g n)))
                                           ((egra g l) - {efids_cur(cgra g n)})))
                              (kgra g)\<close>

inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          a \<in> actors_graph G; enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get : "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G;
        enables I l (Actor a) get; 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)(egra G)
                       ((kgra G)(a := ((kgra G a)(l:= {(x,y). x \<in> agra G l \<and> y \<in> egra G l})))))
                   (delta I)
         \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| put : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> enables I l (Actor a) put \<Longrightarrow>
        I' = Infrastructure (put_graph_efid a l G)(delta I)
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

definition anonymous_actor :: "infrastructure \<Rightarrow> efid \<Rightarrow> identity"
  where
"anonymous_actor I e = (SOME a :: identity. a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I) \<and>
                       e \<in> range(efids_list (InfrastructureTwo.cgra (graphI I) a)))"

lemma anonymous_actor_defO: "InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I) \<noteq> {} \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). inj (efids_list (InfrastructureTwo.cgra (graphI I) a))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI I). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter> 
      (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')))) = {}))) \<Longrightarrow>
    l \<in> nodes (graphI I) \<Longrightarrow> 
    e \<in> (\<Union> a \<in> actors_graph (InfrastructureTwo.graphI I). 
            range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))) 
             \<Longrightarrow>
    \<exists>! a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I). e \<in> range (efids_list (InfrastructureTwo.cgra (graphI I) a))"
  apply (rule ex_ex1I)
  apply blast
 by blast

lemma anonymous_actor_def1a: "InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I) \<noteq> {} \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). inj (efids_list (InfrastructureTwo.cgra (graphI I) a))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI I). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter> 
      (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')))) = {}))) \<Longrightarrow>
    l \<in> nodes (graphI I) \<Longrightarrow> 
    e \<in> (\<Union> a \<in> actors_graph (InfrastructureTwo.graphI I). 
            range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))) 
             \<Longrightarrow>
    anonymous_actor I e \<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I)
    \<and> e \<in> range (efids_list (InfrastructureTwo.cgra (graphI I)(anonymous_actor I e)))"
  apply (drule anonymous_actor_defO, assumption+)
   apply (simp add: anonymous_actor_def)
  by (metis (mono_tags, lifting) someI)

lemma anonymous_actor_def1b: "InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I) \<noteq> {} \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). inj (efids_list (InfrastructureTwo.cgra (graphI I) a))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI I). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter> 
      (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')))) = {}))) \<Longrightarrow>
    l \<in> nodes (graphI I) \<Longrightarrow> 
    e \<in> (\<Union> a \<in> actors_graph (InfrastructureTwo.graphI I). 
            range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))) 
             \<Longrightarrow>
    a' \<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I)
    \<and> e \<in> range (efids_list (InfrastructureTwo.cgra (graphI I) a'))
   \<Longrightarrow> a' = anonymous_actor I e"
  apply (drule anonymous_actor_defO, assumption+)
   apply (simp add: anonymous_actor_def)
  by (metis (no_types, lifting) someI)

definition ref_map :: "[InfrastructureTwo.infrastructure, 
                        [InfrastructureOne.igraph, location] \<Rightarrow> policy set]
                        \<Rightarrow> InfrastructureOne.infrastructure"
  where "ref_map I lp = InfrastructureOne.Infrastructure 
                                 (InfrastructureOne.Lgraph
                                        (InfrastructureTwo.gra (graphI I))
                                        (InfrastructureTwo.agra (graphI I))
                                        (InfrastructureTwo.cgra (graphI I))
                                        (InfrastructureTwo.lgra (graphI I))
                                        (InfrastructureTwo.egra (graphI I))
                                        (InfrastructureTwo.kgra (graphI I)))   
                                                         lp"

lemma delta_invariant[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z')"
  apply clarify
  apply (erule state_transition_in.cases)
  by simp+


lemma same_actors0[rule_format]: "\<forall> z z'.  z \<rightarrow>\<^sub>n z' \<longrightarrow> actors_graph (graphI z) = actors_graph (graphI z')"
proof (clarify, erule state_transition_in.cases)
  show "\<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.move_graph_a a l l' (InfrastructureTwo.graphI I))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z')"
    apply (simp add: InfrastructureTwo.actors_graph_def)
    apply (rule equalityI)
     apply (rule subsetI)
     apply (rule CollectI)
     apply (drule CollectD)
     apply (erule exE, erule conjE)+
    apply (simp add: move_graph_a_def)
     apply (smt (z3) Collect_cong InfrastructureTwo.gra.simps InfrastructureTwo.nodes_def)
    apply (simp add: InfrastructureOne.enables_def move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
     apply (rule subsetI)
     apply (rule CollectI)
     apply (drule CollectD)
     apply (erule exE)+
    apply (erule conjE)+
     apply (smt (z3) InfrastructureTwo.gra.simps InfrastructureTwo.nodes_def mem_Collect_eq)
    using InfrastructureTwo.nodes_def by auto
next show " \<And>z z' G I a l I' g.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra g)
          ((InfrastructureTwo.kgra g)
           (a := (InfrastructureTwo.kgra g a)
              (l := {(x, y). x \<in> InfrastructureTwo.agra G l \<and> y \<in> InfrastructureTwo.egra G l}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z')"
    by (simp add: InfrastructureTwo.actors_graph_def InfrastructureTwo.nodes_def)
next show "\<And>z z' G I a l I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.put_graph_efid a l G)
        (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z')"
    by (simp add: InfrastructureTwo.actors_graph_def InfrastructureTwo.nodes_def InfrastructureTwo.put_graph_efid_def)
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
  apply (erule InfrastructureTwo.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def put_graph_efid_def)+

lemma same_nodes: "(c, s) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> InfrastructureTwo.nodes (graphI c) = InfrastructureTwo.nodes (graphI s)"
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


(* anonymous actor invariant, i.e. we show that any efid that appears in a state, that is, either in  
  the egra component or in the kgra component, is in the range of an efidlist for some actor a
  in the set of actors of the infrastructure. Typical for invariants, we first show that the invariant 
  is preserved in a step, and this is then simply extrapolated by induction to any reachable I has the 
  property if it is reached from an initial I that already had that property.*)
lemma efids_list_eqO: " InfrastructureTwo.efids_list (ef) =
       InfrastructureTwo.efids_list  (InfrastructureTwo.efids_inc_ind ef)"
  by (metis InfrastructureTwo.efids_inc_ind.simps InfrastructureTwo.efids_list.simps efidlist.exhaust)
 

lemma efids_list_eq[rule_format]: "(\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow> 
efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) =
efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a))"
proof (clarify, frule same_actors0, frule same_nodes0, erule state_transition_in.cases)
  show "\<And>z z' G I aa l I' g.
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra g)
          ((InfrastructureTwo.kgra g)
           (aa := (InfrastructureTwo.kgra g aa)
              (l := {(x, y). x \<in> InfrastructureTwo.agra G l \<and> y \<in> InfrastructureTwo.egra G l}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) =
       InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)"
    by force
next show "\<And>z z' G I aa l l' I'.
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       aa \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.move_graph_a aa l l' (InfrastructureTwo.graphI I)) (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) =
       InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)"
    using InfrastructureTwo.move_graph_a_def efids_list_eqO by fastforce
next show
 "\<And>z z' G I aa l I'.
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.put_graph_efid aa l G)
        (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) =
       InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)"
    apply (simp add: move_graph_a_def)
    using InfrastructureTwo.put_graph_efid_def efids_list_eqO by fastforce
qed

lemma efids_list_eq0: "\<And> z z'. (z \<rightarrow>\<^sub>n z') \<Longrightarrow>
\<forall> a. efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) =
efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)"
  by (simp add: efids_list_eq)

(* efids root*)
lemma efids_root_efids_inc_lem: "efids_root (efids_inc_ind el) = efids_root el"
  by (case_tac el, simp add: efids_inc_ind_def efids_root_def)

text \<open> similar to same_nodes we need to prove invariant for reachable states:
       xa \<noteq> a \<Longrightarrow>
       efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) xa) \<noteq>
       efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) a) \<close>
(* efids invariants *)
lemma eroots_inj_inv0: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>  
(inj(\<lambda> x. efids_root(InfrastructureTwo.cgra (InfrastructureTwo.graphI z) x)) \<longrightarrow> 
inj(\<lambda> x. efids_root(InfrastructureTwo.cgra (InfrastructureTwo.graphI z') x)))))"
    apply clarify
  apply (erule InfrastructureTwo.state_transition_in.cases)
  apply (simp add: InfrastructureTwo.move_graph_a_def)
  apply (smt (z3) InfrastructureTwo.efids_root_efids_inc_lem inj_on_cong)
  apply simp
  by (smt InfrastructureTwo.cgra.simps InfrastructureTwo.graphI.simps InfrastructureTwo.put_graph_efid_def efids_root_efids_inc_lem fun_upd_apply inj_on_cong)

lemma eroots_inj_inv[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
\<Longrightarrow> (inj(\<lambda> x. efids_root(InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x)) \<longrightarrow> 
     inj(\<lambda> x. efids_root(InfrastructureTwo.cgra (InfrastructureTwo.graphI y) x)))"
proof (erule rtrancl_induct)
  show "inj (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x)) \<longrightarrow>
    inj (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))" by simp
next show "\<And>y z. (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           inj (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x)) \<longrightarrow>
           inj (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) x)) \<Longrightarrow>
           inj (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x)) \<longrightarrow>
           inj (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) x)) "
    using eroots_inj_inv0 by auto
qed

lemma eroots_inj_on_inv0: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>  
(inj_on(\<lambda> x. efids_root(InfrastructureTwo.cgra (InfrastructureTwo.graphI z) x)) 
           (actors_graph (InfrastructureTwo.graphI z)) \<longrightarrow> 
     inj_on(\<lambda> x. efids_root(InfrastructureTwo.cgra (InfrastructureTwo.graphI z') x))
           (actors_graph (InfrastructureTwo.graphI z')))))"
    apply clarify
  apply (erule InfrastructureTwo.state_transition_in.cases)
    apply (simp add: InfrastructureTwo.move_graph_a_def actors_graph_def inj_on_def
                    InfrastructureTwo.gra.simps InfrastructureTwo.nodes_def)
    apply (erule exE)+
  apply (rule conjI)
    apply (rule impI)+
     apply (rule allI)
  apply (rule conjI)
      apply (rule impI)+
  apply (metis InfrastructureTwo.efids_root_efids_inc_lem)
  apply (metis InfrastructureTwo.efids_root_efids_inc_lem)
  apply force
  using InfrastructureTwo.actors_graph_def InfrastructureTwo.nodes_def apply force
  by (smt (z3) InfrastructureTwo.cgra.simps InfrastructureTwo.efids_root_efids_inc_lem InfrastructureTwo.graphI.simps InfrastructureTwo.put_graph_efid_def InfrastructureTwo.same_actors0 InfrastructureTwo.state_transition_in.put fun_upd_apply inj_on_def)

lemma eroots_inj_on_inv[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
\<Longrightarrow> (inj_on(\<lambda> x. efids_root(InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x)) 
           (actors_graph (InfrastructureTwo.graphI I)) \<longrightarrow> 
     inj_on(\<lambda> x. efids_root(InfrastructureTwo.cgra (InfrastructureTwo.graphI y) x))
           (actors_graph (InfrastructureTwo.graphI y)))"
proof (erule rtrancl_induct)
show "inj_on (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))
     (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I)) \<longrightarrow>
    inj_on (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))
     (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I))"
  by simp
next show "\<And>y z. (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           inj_on (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))
            (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I)) \<longrightarrow>
           inj_on (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) x))
            (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI y)) \<Longrightarrow>
           inj_on (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))
            (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I)) \<longrightarrow>
           inj_on (\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) x))
            (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z))"
    by (simp add: eroots_inj_on_inv0)
qed



(* *)
lemma efids_list_disjoint: "(\<forall> (z :: InfrastructureTwo.infrastructure). (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI z). a \<noteq> a' \<longrightarrow> 
(range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) \<inter> 
 range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a'))) = {}))
\<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI z'). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI z'). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)) \<inter> 
 (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a')))) = {})))
))"
    apply clarify
  apply (erule InfrastructureTwo.state_transition_in.cases)
  apply (smt (z3) InfrastructureTwo.efids_list_eq0 InfrastructureTwo.same_actors0 InfrastructureTwo.state_transition_in.move)
   apply (simp add: InfrastructureTwo.actors_graph_def InfrastructureTwo.nodes_def)
  apply (simp add: put_graph_efid_def)
  by (metis InfrastructureTwo.graphI.simps InfrastructureTwo.put_graph_efid_def InfrastructureTwo.same_actors0 InfrastructureTwo.state_transition_in.put efidlist.exhaust efids_inc_ind.simps efids_list.simps)

lemma ran_efidslist_disjoint:
"(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a')))) = {})))
\<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI z'). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI z'). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)) \<inter> 
 (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a')))) = {})))
))"
  by (rule efids_list_disjoint)


lemma ran_efids_list_disjoint_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI I). a \<noteq> a' \<longrightarrow>
((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter> 
 (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')))) = {}))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI y). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI y). a \<noteq> a' \<longrightarrow>
((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) a)) \<inter> 
 (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) a')))) = {})))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
              \<forall>a'\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter>
                 range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')) =
                 {} \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI y).
              \<forall>a'\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI y).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) a)) \<inter>
                 range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) a')) =
                 {} \<Longrightarrow>
           \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
              \<forall>a'\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) \<inter>
                 range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a')) =
                 {}"
    by (simp add: ran_efidslist_disjoint)
qed



(* efids_cur inj_on*)
lemma efids_cur_in_efids_listO: "a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I) \<Longrightarrow>
           efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)
         \<in> range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))"
  apply (case_tac "(InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)")
  by simp

lemma efids_cur_in_efids_list: "a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I) \<Longrightarrow>
           efids_cur (efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
         \<in> range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))"
  apply (case_tac "(InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)")
  by simp

lemma inj_on_put_preserve0: "\<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
          \<forall>a'\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
             a \<noteq> a' \<longrightarrow>
             range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter>
             range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')) =
             {} \<Longrightarrow>
             \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
             efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<Longrightarrow>
             inj_on (\<lambda>x. efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))
                    (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I)) \<Longrightarrow>
            a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I) \<Longrightarrow>
              inj_on ((\<lambda>x. efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))
                      (a:= efids_cur (efids_inc_ind ((InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)))))
        (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I))"
  apply (rule Fun.inj_on_fun_updI)
   apply blast
  apply (unfold image_def)
  apply (rule notI)
  apply (drule CollectD)
  apply (erule bexE)
  apply (case_tac "x = a")
   apply fastforce
  apply (drule_tac x = a in bspec)
   apply assumption
  apply (rotate_tac -1)
  apply (drule_tac x = x in bspec)
    apply assumption
   apply (subgoal_tac "efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x) \<in>
                       range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))")
   apply (subgoal_tac "efids_cur (efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<in>
                     range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))")
    apply fastforce
  apply (simp add: efids_list_def)
   prefer 2
  apply (case_tac "InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x")
  apply simp
  by (metis efidlist.exhaust efidlist.simps(3) efids_cur_in_efids_list efids_list.simps)


lemma inj_on_put_preserve: "\<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
          \<forall>a'\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
             a \<noteq> a' \<longrightarrow>
             range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter>
             range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')) =
             {} \<Longrightarrow>
       \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
             efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a) \<noteq>
          efids_cur(efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<Longrightarrow>
       inj_on (\<lambda>x. efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))
        (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I)) \<Longrightarrow>
      inj_on (\<lambda>x. efids_cur
              (if x = a then efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)
               else InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))
        (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I))"
  by (smt (verit, ccfv_SIG) fun_upd_apply inj_on_cong inj_on_put_preserve0)

lemma efids_list_inj_imp_inc_ind_not_eq[rule_format]: " (\<forall> a \<in> actors_graph (InfrastructureTwo.graphI z). 
 inj (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) \<longrightarrow>
      efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)))"
proof (clarify, simp add: efids_inc_ind_def efids_cur_def efids_list_def, case_tac "InfrastructureTwo.graphI z", simp)
  show "\<And>a x1 x2 x3 x4 x5 x6.
       a \<in> InfrastructureTwo.actors_graph (InfrastructureTwo.igraph.Lgraph x1 x2 x3 x4 x5 x6) \<Longrightarrow>
       inj (rec_efidlist (\<lambda>e n ef. ef) (x3 a)) \<Longrightarrow>
       rec_efidlist (\<lambda>e n ef. ef n) (x3 a) = rec_efidlist (\<lambda>e n ef. ef n) (rec_efidlist (\<lambda>e n. Efids e (Suc n)) (x3 a)) \<Longrightarrow>
       InfrastructureTwo.graphI z = InfrastructureTwo.igraph.Lgraph x1 x2 x3 x4 x5 x6 \<Longrightarrow> False"
    by (smt (z3) efidlist.exhaust efidlist.rec n_not_Suc_n the_inv_f_f)
qed


(* agra \<longrightarrow> egra invariants *) 
lemma actor_unique_loc_lem00[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l' \<longrightarrow> l = l')) 
        \<longrightarrow> (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z') \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z') l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z') l' \<longrightarrow> l = l'))"
  apply (rule allI)+
  apply (rule impI)+
  apply (erule InfrastructureTwo.state_transition_in.cases)
    apply (simp add: move_graph_a_def)
  apply auto[1]
  using InfrastructureTwo.agra.simps InfrastructureTwo.graphI.simps apply presburger
  using InfrastructureTwo.agra.simps InfrastructureTwo.graphI.simps InfrastructureTwo.put_graph_efid_def by presburger


lemma actor_unique_loc_lem0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  (\<forall> l'. l' \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l \<longrightarrow> 
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l' \<longrightarrow> l = l'))) 
        \<longrightarrow> (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z') \<longrightarrow>  (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z') l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z') l' \<longrightarrow> l = l')))"
  apply (rule allI)+
  apply (rule impI)+
  apply (erule InfrastructureTwo.state_transition_in.cases)
    apply (simp add: move_graph_a_def)
  using InfrastructureTwo.atI_def apply force
  using InfrastructureTwo.agra.simps InfrastructureTwo.graphI.simps apply presburger
  using InfrastructureTwo.agra.simps InfrastructureTwo.graphI.simps InfrastructureTwo.put_graph_efid_def by presburger
thm actor_unique_loc_lem0

lemma actor_unique_loc_lem0a: "z \<rightarrow>\<^sub>n z' \<Longrightarrow>  nodes (graphI z) = nodes (graphI z') \<Longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l' \<longrightarrow> l = l'))
        \<Longrightarrow> l \<in> nodes (graphI z') \<Longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z') l \<Longrightarrow> 
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z') l' \<Longrightarrow> l = l'"
  using actor_unique_loc_lem00 by presburger

lemma actor_unique_loc_lem[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI y) \<longrightarrow> 
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI y) l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI y) l' \<longrightarrow> l = l'))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a l l'.
              l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI I) \<longrightarrow>
              a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI I) l \<longrightarrow>
              a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI y) \<longrightarrow>
              a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI y) l \<longrightarrow>
              a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI y) l' \<longrightarrow> l = l' \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z) \<longrightarrow>
              a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI z) l \<longrightarrow>
              a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI z) l' \<longrightarrow> l = l'"
    by (metis CollectD InfrastructureTwo.same_nodes actor_unique_loc_lem0a case_prodD rtrancl.rtrancl_into_rtrancl)
qed

lemma efid_in_range_invariantO: "(\<forall> (z :: InfrastructureTwo.infrastructure) z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow> 
         (\<forall> l \<in> InfrastructureTwo.nodes (graphI z).
         (\<forall> e \<in> (InfrastructureTwo.egra (InfrastructureTwo.graphI z) l).
         (\<exists> a \<in> InfrastructureTwo.actors_graph (graphI z). e \<in> range (efids_list (InfrastructureTwo.cgra (graphI z) a)))))
          \<longrightarrow>  (\<forall> l \<in> nodes (graphI z').
         (\<forall> e \<in> (egra (InfrastructureTwo.graphI z') l). 
         (\<exists> a \<in> actors_graph (graphI z'). e \<in> range (efids_list (InfrastructureTwo.cgra (graphI z') a))))))"
proof (clarify, frule same_actors0, frule same_nodes0, frule efids_list_eq0, erule state_transition_in.cases)
show "\<And>z z' l e G I a la I'.
       \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
          \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI z) l.
             \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
                e \<in> range (InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       e \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI z') l \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       \<forall>a. InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) =
           InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureTwo.enables I la (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra G)
          ((InfrastructureTwo.kgra G)
           (a := (InfrastructureTwo.kgra G a)
              (la := {(x, y). x \<in> InfrastructureTwo.agra G la \<and> y \<in> InfrastructureTwo.egra G la}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z').
          e \<in> range (InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a))"
    by simp
next show "\<And>z z' l e G I a la I'.
       \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
          \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI z) l.
             \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
                e \<in> range (InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       e \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI z') l \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       \<forall>a. InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) =
           InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureTwo.enables I la (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.put_graph_efid a la G)
        (InfrastructureTwo.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z').
          e \<in> range (InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a))"
    by (smt (z3) Diff_iff InfrastructureTwo.actors_graph_def InfrastructureTwo.atI_def InfrastructureTwo.egra.simps InfrastructureTwo.graphI.simps InfrastructureTwo.put_graph_efid_def UNIV_I efidlist.exhaust efids_cur.simps efids_inc_ind.simps efids_list.simps fun_upd_apply image_eqI insert_iff mem_Collect_eq)
next show "\<And>z z' l e G I a la l' I'.
       \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
          \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI z) l.
             \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
                e \<in> range (InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       e \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI z') l \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.move_graph_a a la l' (InfrastructureTwo.graphI I)) (InfrastructureTwo.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z').
          e \<in> range (InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a))"
    apply (simp add: move_graph_a_def)
    apply (case_tac "a \<in> ((agra (InfrastructureTwo.graphI I)) la) &  a \<notin> ((agra (InfrastructureTwo.graphI I)) l')")
     prefer 2
     apply (simp add: move_graph_a_def)
     apply (rule impI)+
     apply meson
    apply (rule conjI)
     apply (rule impI)+
    apply simp
    apply (case_tac "l = l'")
    prefer 2
      apply (metis Diff_iff efids_list_eqO fun_upd_apply)
     apply simp
    apply (case_tac "l = la")
      apply force
     apply simp
    apply (erule disjE)
     apply (rule_tac x = a in bexI)
    apply simp
    using InfrastructureTwo.efids_cur_in_efids_list efids_list_eqO apply presburger
    apply force
    apply (metis efids_list_eqO)
    by meson
qed

(* variation for applicability*)
lemma efid_in_range_invariantOa: "(z \<rightarrow>\<^sub>n z') \<Longrightarrow> 
         (\<forall> l \<in> nodes (graphI z).
         (\<forall> e \<in> (egra (InfrastructureTwo.graphI z) l).
         (\<exists> a \<in> actors_graph (graphI z). e \<in> range (efids_list (InfrastructureTwo.cgra (graphI z) a)))))
          \<Longrightarrow>  (\<forall> l \<in> nodes (graphI z').
         (\<forall> e \<in> (egra (InfrastructureTwo.graphI z') l). 
         (\<exists> a \<in> actors_graph (graphI z'). e \<in> range (efids_list (InfrastructureTwo.cgra (graphI z') a)))))"
  using efid_in_range_invariantO by presburger

lemma efids_in_range_invariantOO[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
        \<Longrightarrow> (\<forall> l \<in> nodes (graphI I).
            \<forall> e \<in> (egra (InfrastructureTwo.graphI I) l).
         \<exists> a \<in> actors_graph (graphI I). e \<in> range (efids_list (InfrastructureTwo.cgra (graphI I) a)))
       \<Longrightarrow> (\<forall> l \<in> nodes (graphI y).
           \<forall> e \<in> (egra (InfrastructureTwo.graphI y) l).
         \<exists> a \<in> actors_graph (graphI y). e \<in> range (efids_list (InfrastructureTwo.cgra (graphI y) a)))"
proof (erule rtrancl_induct)
  show "\<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I).
       \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI I) l.
          \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
             e \<in> range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<Longrightarrow>
    \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I).
       \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI I) l.
          \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
             e \<in> range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))"
    by blast
next show "\<And>y z. \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I).
              \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI I) l.
                 \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
                    e \<in> range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI y).
              \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI y) l.
                 \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI y).
                    e \<in> range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) a)) \<Longrightarrow>
           \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
              \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI z) l.
                 \<exists>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
                    e \<in> range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) "
    using efid_in_range_invariantO by auto
qed

lemma anonymous_actor_eq: "(z \<rightarrow>\<^sub>n z') \<Longrightarrow> 
InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) \<noteq> {} \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI z). inj (efids_list (InfrastructureTwo.cgra (graphI z) a))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI z). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) \<inter> 
      (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a')))) = {}))) \<Longrightarrow>
    e \<in> (\<Union> a \<in> actors_graph (InfrastructureTwo.graphI z). 
            range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)))
\<Longrightarrow>    anonymous_actor z e = anonymous_actor z' e"
  by (smt (verit, ccfv_threshold) InfrastructureTwo.actors_graph_def InfrastructureTwo.same_actors0 UN_iff anonymous_actor_def1b efids_list_eq0 mem_Collect_eq)

(* *)
lemma efids_cur_eq_egra[rule_format]: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureTwo.graphI z).
\<forall> e \<in> (InfrastructureTwo.egra (InfrastructureTwo.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureTwo.graphI z) l. 
     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a))) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureTwo.graphI z').
\<forall> e \<in> (InfrastructureTwo.egra (InfrastructureTwo.graphI z') l).
 (\<exists> a \<in> agra (InfrastructureTwo.graphI z') l. 
     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)))))"
proof (clarify, frule same_actors0, frule same_nodes0, rule state_transition_in.cases, assumption)
  show "\<And>z z' l e G I a la l' I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z) \<longrightarrow>
          a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI z) l \<longrightarrow>
          a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
          \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI z) l.
             \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI z) l.
                e = InfrastructureTwo.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       e \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI z') l \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.move_graph_a a la l' (InfrastructureTwo.graphI I)) (InfrastructureTwo.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI z') l.
          e = InfrastructureTwo.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)"
    apply (simp add: move_graph_a_def)
    by (smt (z3) DiffE Diff_empty Diff_insert0 fun_upd_other fun_upd_same insertE insert_Diff1 mk_disjoint_insert singleton_iff)
next show "\<And>z z' l e G I a la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
          \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI z) l.
             \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI z) l.
                e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       e \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI z') l \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       InfrastructureTwo.enables I la (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra G)
          ((InfrastructureTwo.kgra G)
           (a := (InfrastructureTwo.kgra G a)
              (la := {(x, y). x \<in> InfrastructureTwo.agra G la \<and> y \<in> InfrastructureTwo.egra G la}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI z') l.
          e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)"
    by simp
next show "\<And>z z' l e G I a la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z) \<longrightarrow>
          a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI z) l \<longrightarrow>
          a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
          \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI z) l.
             \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI z) l.
                e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       e \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI z') l \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureTwo.enables I la (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.put_graph_efid a la G)
        (InfrastructureTwo.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI z') l.
          e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z') a)"
    apply (unfold put_graph_efid_def)
    apply (case_tac "l = la")
    apply (smt (z3) DiffE InfrastructureTwo.agra.simps InfrastructureTwo.atI_def InfrastructureTwo.cgra.simps InfrastructureTwo.egra.simps InfrastructureTwo.graphI.simps fun_upd_apply insertCI insertE)
    apply (drule_tac x = l in bspec)
     apply metis
    apply (subgoal_tac "e \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI z) l ")
    prefer 2
    apply fastforce
    apply (drule_tac x = e in bspec, assumption)
    apply (erule bexE)
    apply (rule_tac x = aa in bexI)
     apply (simp add: atI_def)
     apply (subgoal_tac "aa \<noteq> a")
      apply simp
    prefer 2
    using InfrastructureTwo.agra.simps InfrastructureTwo.graphI.simps apply presburger
    by meson
qed

lemma efids_cur_eq_egra_refl[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureTwo.graphI I).
\<forall> e \<in> (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l).
 (\<exists> a \<in> agra (InfrastructureTwo.graphI I) l. 
     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureTwo.graphI y).
\<forall> e \<in> (InfrastructureTwo.egra (InfrastructureTwo.graphI y) l).
 (\<exists> a \<in> agra (InfrastructureTwo.graphI y) l. 
     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) a)))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a l l'.
              l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI I) \<longrightarrow>
              a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI I) l \<longrightarrow>
              a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           (\<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I).
               \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI I) l.
                  \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI I) l.
                     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<longrightarrow>
           (\<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI y).
               \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI y) l.
                  \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI y) l.
                     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) a)) \<Longrightarrow>
           (\<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I).
               \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI I) l.
                  \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI I) l.
                     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<longrightarrow>
           (\<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
               \<forall>e\<in>InfrastructureTwo.egra (InfrastructureTwo.graphI z) l.
                  \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI z) l.
                     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a))"
    by (simp add: Pair_inject actor_unique_loc_lem case_prodE efids_cur_eq_egra)
qed

(* efids_cur injective*)
lemma efids_cur_inj_on_inv0[rule_format]: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a')))) = {}))) \<longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureTwo.graphI z). 
      efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a))) \<longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureTwo.cgra (InfrastructureTwo.graphI z) x)) 
           (actors_graph (InfrastructureTwo.graphI z)) \<longrightarrow> 
     inj_on(\<lambda> x. efids_cur(InfrastructureTwo.cgra (InfrastructureTwo.graphI z') x))
           (actors_graph (InfrastructureTwo.graphI z')))))"
  by (smt (verit, ccfv_SIG) InfrastructureTwo.efids_cur_in_efids_listO InfrastructureTwo.ran_efidslist_disjoint disjoint_iff inj_on_def)

lemma efids_cur_inj_on_inv_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI I). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter> 
 (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')))) = {}))) \<Longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureTwo.graphI I). 
      efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))) \<Longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x)) 
           (actors_graph (InfrastructureTwo.graphI I))) \<Longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureTwo.cgra (InfrastructureTwo.graphI y) x)) 
           (actors_graph (InfrastructureTwo.graphI y)))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
              \<forall>a'\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter>
                 range (InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')) =
                 {} \<Longrightarrow>
           \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
              InfrastructureTwo.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a) \<noteq>
              InfrastructureTwo.efids_cur
               (InfrastructureTwo.efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<Longrightarrow>
           inj_on (\<lambda>x. InfrastructureTwo.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x))
            (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I)) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           inj_on (\<lambda>x. InfrastructureTwo.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) x))
            (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI y)) \<Longrightarrow>
           inj_on (\<lambda>x. InfrastructureTwo.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) x))
            (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z)) "
    by (smt (verit, del_insts) InfrastructureTwo.efids_cur_in_efids_listO InfrastructureTwo.efids_list_eq InfrastructureTwo.ran_efids_list_disjoint_refl InfrastructureTwo.same_actors0 Int_iff case_prod_conv empty_iff inj_on_def mem_Collect_eq)
qed

(* Invariant for refmapTwo_lem *)
lemma refmap_lem_egra_unique_prepO: "(\<forall> l \<in> nodes(InfrastructureTwo.graphI z).
\<forall> e \<in> (InfrastructureTwo.egra (InfrastructureTwo.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureTwo.graphI z) l. 
     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)))
\<Longrightarrow> (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI z) l' \<longrightarrow> l = l')) 
\<Longrightarrow> (inj_on(\<lambda> x. efids_cur(InfrastructureTwo.cgra (InfrastructureTwo.graphI z) x)) 
           (actors_graph (InfrastructureTwo.graphI z)))
\<Longrightarrow>  (\<forall> a \<in> InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z). 
     (\<forall> l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z). 
       (\<forall> l' \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z). 
             (a @\<^bsub>(InfrastructureTwo.graphI z)\<^esub> l) \<longrightarrow>
        (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)
       \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI z) l') 
       \<longrightarrow> l = l' )))"
  apply clarify
  apply (drule_tac x = l' in bspec, assumption)
  apply (rotate_tac -1)
  apply (drule_tac x = "InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI z) a)" in bspec, assumption)
  apply (erule bexE)
  apply (simp add: atI_def)
  apply (subgoal_tac "a = aa")
   apply blast
  apply (erule inj_onD)
    apply (subgoal_tac " InfrastructureOne.efids_cur =  InfrastructureTwo.efids_cur")
     prefer 2
    apply (simp add: InfrastructureOne.efids_cur_def  InfrastructureTwo.efids_cur_def)
    apply simp
  apply blast
  using InfrastructureTwo.actors_graph_def by blast

lemma refmap_lem_egra_unique_refl[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureTwo.graphI I).
\<forall> e \<in> (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l).
 (\<exists> a \<in> agra (InfrastructureTwo.graphI I) l. 
     e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)))
\<Longrightarrow> (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureTwo.agra (InfrastructureTwo.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI I). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) \<inter> 
 (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a')))) = {}))) \<Longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureTwo.graphI I). 
      efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)))
\<Longrightarrow> (inj_on(\<lambda> x. efids_cur(InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x)) 
           (actors_graph (InfrastructureTwo.graphI I)))
\<Longrightarrow>  (\<forall> a \<in> InfrastructureTwo.actors_graph (InfrastructureTwo.graphI y). 
     (\<forall> l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI y). 
       (\<forall> l' \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI y). 
             (a @\<^bsub>(InfrastructureTwo.graphI y)\<^esub> l) \<longrightarrow>
        (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI y) a)
       \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI y) l') 
       \<longrightarrow> l = l' )))"
  apply (rule refmap_lem_egra_unique_prepO)
  apply (simp add: InfrastructureTwo.efids_cur_eq_egra_refl)
  using InfrastructureTwo.actor_unique_loc_lem apply presburger
  by (rule efids_cur_inj_on_inv_refl, assumption+)

lemma delta_ext_step_imp_refl: "(\<forall>z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>  (\<forall> l \<in> nodes (graphI z).
       \<forall> xa \<in> InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l. 
            xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l)) \<Longrightarrow>
     (I, y) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow> xa \<in> InfrastructureTwo.delta I (InfrastructureTwo.graphI I) l \<Longrightarrow>
       xa \<in> InfrastructureTwo.delta y (InfrastructureTwo.graphI y) l"
proof (erule rtrancl_induct)
  show "\<forall>z z'.
       z \<rightarrow>\<^sub>n z' \<longrightarrow>
       (\<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
           \<forall>xa\<in>InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l.
              xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l) \<Longrightarrow>
    l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI I) \<Longrightarrow>
    xa \<in> InfrastructureTwo.delta I (InfrastructureTwo.graphI I) l \<Longrightarrow>
    xa \<in> InfrastructureTwo.delta I (InfrastructureTwo.graphI I) l"
    by blast
next show "\<And>y z. \<forall>z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>
                  (\<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
                      \<forall>xa\<in>InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l.
                         xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l) \<Longrightarrow>
           l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI I) \<Longrightarrow>
           xa \<in> InfrastructureTwo.delta I (InfrastructureTwo.graphI I) l \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           xa \<in> InfrastructureTwo.delta y (InfrastructureTwo.graphI y) l \<Longrightarrow>
           xa \<in> InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l "
    using InfrastructureTwo.same_nodes by blast
qed

lemma put_enables_invariant: "(\<forall> (z :: InfrastructureTwo.infrastructure).
        (\<forall> (z' :: InfrastructureTwo.infrastructure). 
             (z \<rightarrow>\<^sub>n z')  \<longrightarrow>  
       (\<forall> l \<in> nodes (graphI z).
       \<forall> xa \<in> InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l. 
            xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l) \<longrightarrow>
             (\<forall> a \<in> actors_graph (graphI z). \<forall> l \<in> nodes (graphI z).
                       (enables z l (Actor a) put)) \<longrightarrow> 
             (\<forall> a \<in> actors_graph (graphI z). \<forall> l \<in> nodes (graphI z).
                       (enables z' l (Actor a) put))))"
proof (clarify, frule same_actors0, frule same_nodes0, erule state_transition_in.cases)
  show "\<And>z z' a l G I aa la l' I'.
       \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
          \<forall>xa\<in>InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l.
             xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l \<Longrightarrow>
       \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
          \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z). InfrastructureTwo.enables z l (Actor a) put \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z) \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       aa \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.move_graph_a aa la l' (InfrastructureTwo.graphI I)) (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureTwo.enables z' l (Actor a) put"
    apply (simp add: InfrastructureTwo.enables_def)
    by meson
next show "\<And>z z' a l G I aa la I'.
       \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
          \<forall>xa\<in>InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l.
             xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l \<Longrightarrow>
       \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
          \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z). InfrastructureTwo.enables z l (Actor a) put \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z) \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       InfrastructureTwo.enables I la (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra G)
          ((InfrastructureTwo.kgra G)
           (aa := (InfrastructureTwo.kgra G aa)
              (la := {(x, y). x \<in> InfrastructureTwo.agra G la \<and> y \<in> InfrastructureTwo.egra G la}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureTwo.enables z' l (Actor a) put"
    apply (simp add: InfrastructureTwo.enables_def)
    by meson
next show "\<And>z z' a l G I aa la I'.
       \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
          \<forall>xa\<in>InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l.
             xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l \<Longrightarrow>
       \<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
          \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z). InfrastructureTwo.enables z l (Actor a) put \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z) \<Longrightarrow>
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z) =
       InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z') \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI z) = InfrastructureTwo.nodes (InfrastructureTwo.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureTwo.enables I la (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.put_graph_efid aa la G)
        (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureTwo.enables z' l (Actor a) put "
    apply (simp add: InfrastructureTwo.enables_def)
    by meson
qed

lemma put_enables_invariant_ref: "
(\<forall>z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>  (\<forall> l \<in> nodes (graphI z).
       \<forall> xa \<in> InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l. 
            xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l)) \<Longrightarrow>
     (I, y) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). \<forall> l \<in> nodes (graphI I).
                       (enables I l (Actor a) put)) \<longrightarrow> 
(\<forall> a \<in> actors_graph (graphI y). \<forall> l \<in> nodes (graphI y).
                       (enables y l (Actor a) put))"
proof (erule rtrancl_induct)
  show " \<forall>z z'.
       z \<rightarrow>\<^sub>n z' \<longrightarrow>
       (\<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
           \<forall>xa\<in>InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l.
              xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l) \<Longrightarrow>
    (\<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
        \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I). InfrastructureTwo.enables I l (Actor a) put) \<longrightarrow>
    (\<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
        \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I). InfrastructureTwo.enables I l (Actor a) put)"
    by blast
next show "\<And>y z. \<forall>z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>
                  (\<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z).
                      \<forall>xa\<in>InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l.
                         xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           (\<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
               \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I). InfrastructureTwo.enables I l (Actor a) put) \<longrightarrow>
           (\<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI y).
               \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI y). InfrastructureTwo.enables y l (Actor a) put) \<Longrightarrow>
           (\<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI I).
               \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I). InfrastructureTwo.enables I l (Actor a) put) \<longrightarrow>
           (\<forall>a\<in>InfrastructureTwo.actors_graph (InfrastructureTwo.graphI z).
               \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI z). InfrastructureTwo.enables z l (Actor a) put) "
    by (metis InfrastructureTwo.enables_def InfrastructureTwo.same_actors0 InfrastructureTwo.same_nodes0 case_prodD mem_Collect_eq)
qed

lemma put_enables_invariant_refO: "
     (I, y) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> l \<in> nodes (graphI I).
       \<forall> xa \<in> InfrastructureTwo.delta I (InfrastructureTwo.graphI I) l. 
            xa \<in> InfrastructureTwo.delta y (InfrastructureTwo.graphI y) l) \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). \<forall> l \<in> nodes (graphI I).
                       (enables I l (Actor a) put)) \<longrightarrow> 
(\<forall> a \<in> actors_graph (graphI y). \<forall> l \<in> nodes (graphI y).
                       (enables y l (Actor a) put))"
  by (metis InfrastructureTwo.enables_def InfrastructureTwo.same_actors InfrastructureTwo.same_nodes)

lemma put_enables_invariant_refOO: "
     (I, y) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> y. (I, y) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
(\<forall> l \<in> nodes (graphI I).
       \<forall> xa \<in> InfrastructureTwo.delta I (InfrastructureTwo.graphI I) l. 
            xa \<in> InfrastructureTwo.delta y (InfrastructureTwo.graphI y) l)) \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). \<forall> l \<in> nodes (graphI I).
                       (enables I l (Actor a) put)) \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI y). \<forall> l \<in> nodes (graphI y).
                       (enables y l (Actor a) put))"
  by (metis InfrastructureTwo.enables_def InfrastructureTwo.same_actors InfrastructureTwo.same_nodes)

(* We can indeed already show that global_policyT'' is true in this level.
   The disjointness of kgras can be shown from disjointness of egras and does imply (see CoronaAppTwo)
   that non idenitifability holds for subsets L \<subseteq> nodes (graphI I) bigger than 2.  *)
lemma all_kgra_disjoint_refl[rule_format]: "(I  \<rightarrow>\<^sub>n* y) \<Longrightarrow> 
\<exists> l \<in> nodes (graphI I). \<exists> l' \<in> nodes (graphI I). l \<noteq> l' \<Longrightarrow>
  (\<forall> a \<in> actors_graph  (graphI I).  
     (\<forall> l \<in> nodes (graphI I). \<forall> l' \<in> nodes (graphI I). 
         (l \<noteq> l' \<longrightarrow> (kgra (graphI I) a l) \<inter> kgra(graphI I) a l' = {}))) \<longrightarrow>
  (\<forall> a \<in> actors_graph  (graphI y). 
     (\<forall> l \<in> nodes (graphI y). \<forall> l' \<in> nodes (graphI y). 
         (l \<noteq> l' \<longrightarrow> (kgra (graphI y) a l) \<inter> kgra(graphI y) a l' = {})))"
  oops

end

 