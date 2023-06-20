theory InfrastructureOne
  imports CoronaApp
begin

text \<open>This is the new element for refining the Ephemeral Id -- a list
     of ephemeral ids repreented as a function from nat to the efid type. 
     This function needs to be unique and reversible so it must be injective and
     also for all actors the ranges should be disjoint. These properties are
     not part of the actual type but are proved as invariants. In applications
     (e.g. CoronaApp) they need to be shown for initial states and then the
     invariants can be applied to show that they hold in any reachable state.\<close>
datatype efidlist = Efids "efid" "nat" "nat \<Rightarrow> efid"

primrec efids_root :: "efidlist \<Rightarrow> efid"
  where "efids_root (Efids e n el) = e"
primrec efids_index :: "efidlist \<Rightarrow> nat"
  where "efids_index (Efids e n el) = n"
primrec efids_inc_ind :: "efidlist \<Rightarrow> efidlist"
  where "efids_inc_ind (Efids e n ef) = (Efids e (Suc n) ef) "
primrec efids_cur:: "efidlist \<Rightarrow> efid"
  where "efids_cur (Efids e n ef) = ef n"
primrec efids_list :: "efidlist \<Rightarrow> nat \<Rightarrow> efid"
  where "efids_list (Efids e n ef) = ef"
definition repl_efr :: "efidlist \<Rightarrow> efid"
  where "repl_efr el \<equiv> efids_root el" 

datatype igraph = Lgraph "(location * location)set" 
                           "location \<Rightarrow> identity set"
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
                    (cgra g) 
                    (lgra g)
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then
                       ((egra g)(l := (egra g l) - {efids_cur(cgra g n)}))
                                (l' := insert (efids_cur(cgra g n))(egra g l'))
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
          (a) \<in> actors_graph(graphI I); enables I l' (Actor a) move;
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
"anonymous_actor I e = (SOME a :: identity. a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<and>
                       e \<in> range(efids_list (InfrastructureOne.cgra (graphI I) a)))"

lemma anonymous_actor_defO: "InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<noteq> {} \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). inj (efids_list (InfrastructureOne.cgra (graphI I) a))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI I). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter> 
      (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')))) = {}))) \<Longrightarrow>
    l \<in> nodes (graphI I) \<Longrightarrow> 
    e \<in> (\<Union> a \<in> actors_graph (InfrastructureOne.graphI I). 
            range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))) 
             \<Longrightarrow>
    \<exists>! a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I). e \<in> range (efids_list (InfrastructureOne.cgra (graphI I) a))"
  apply (rule ex_ex1I)
  apply blast
 by blast

lemma anonymous_actor_def1a: "InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<noteq> {} \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). inj (efids_list (InfrastructureOne.cgra (graphI I) a))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI I). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter> 
      (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')))) = {}))) \<Longrightarrow>
    l \<in> nodes (graphI I) \<Longrightarrow> 
    e \<in> (\<Union> a \<in> actors_graph (InfrastructureOne.graphI I). 
            range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))) 
             \<Longrightarrow>
    anonymous_actor I e \<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I)
    \<and> e \<in> range (efids_list (InfrastructureOne.cgra (graphI I)(anonymous_actor I e)))"
  apply (drule anonymous_actor_defO, assumption+)
   apply (simp add: anonymous_actor_def)
  by (metis (mono_tags, lifting) someI)

lemma anonymous_actor_def1b: "InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<noteq> {} \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). inj (efids_list (InfrastructureOne.cgra (graphI I) a))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI I). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter> 
      (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')))) = {}))) \<Longrightarrow>
    l \<in> nodes (graphI I) \<Longrightarrow> 
    e \<in> (\<Union> a \<in> actors_graph (InfrastructureOne.graphI I). 
            range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))) 
             \<Longrightarrow>
    a' \<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I)
    \<and> e \<in> range (efids_list (InfrastructureOne.cgra (graphI I) a'))
   \<Longrightarrow> a' = anonymous_actor I e"
  apply (drule anonymous_actor_defO, assumption+)
   apply (simp add: anonymous_actor_def)
  by (metis (no_types, lifting) someI)


definition ref_map :: "[InfrastructureOne.infrastructure, 
                        [Infrastructure.igraph, Infrastructure.location] \<Rightarrow> policy set]
                        \<Rightarrow> Infrastructure.infrastructure"
  where "ref_map I lp = Infrastructure.Infrastructure 
                                 (Infrastructure.Lgraph
                                        (InfrastructureOne.gra (graphI I))
                                        (InfrastructureOne.agra (graphI I))
                                        (\<lambda> h:: identity. repl_efr 
                                           ((InfrastructureOne.cgra (graphI I)) h))
                                        (InfrastructureOne.lgra (graphI I))
                                        (\<lambda> l :: Infrastructure.location. 
                                           (\<lambda> a. 
                                              efids_root (InfrastructureOne.cgra (graphI I) a)) ` 
                                                     (InfrastructureOne.agra (graphI I) l))
                                        (\<lambda> a :: identity. \<lambda> l :: Infrastructure.location.
                                            if (a \<in> (InfrastructureOne.actors_graph(graphI I)) \<and> l \<in> (InfrastructureOne.nodes (graphI I)))
                                            then ((\<lambda> (x,y).(x, efids_root(InfrastructureOne.cgra (graphI I)(anonymous_actor I y))))
                                                             `(InfrastructureOne.kgra (graphI I)) a l)
                                            else {}))   
                                                         lp"

lemma delta_invariant: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z')"
  apply clarify
  apply (erule state_transition_in.cases)
  by simp+

lemma same_actors0[rule_format]: "\<forall> z z'.  z \<rightarrow>\<^sub>n z' \<longrightarrow> actors_graph (graphI z) = actors_graph (graphI z')"
proof (clarify, erule state_transition_in.cases)
  show "\<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes G \<Longrightarrow>
       a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
       InfrastructureOne.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI I)) (InfrastructureOne.delta I) \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z')"
    apply (simp add: InfrastructureOne.actors_graph_def)
    apply (rule equalityI)
     apply (rule subsetI)
     apply (rule CollectI)
     apply (drule CollectD)
     apply (erule exE, erule conjE)+
    apply (simp add: move_graph_a_def)
  proof -
  fix z :: InfrastructureOne.infrastructure and z' :: InfrastructureOne.infrastructure and G :: InfrastructureOne.igraph and I :: InfrastructureOne.infrastructure and a :: "char list" and l :: location and l' :: location and I' :: InfrastructureOne.infrastructure and x :: "char list" and y :: location and ya :: location
  assume a1: "G = InfrastructureOne.graphI I"
    assume a2: "l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I)"
    assume a3: "l' \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I)"
    assume a4: "ya \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I)"
assume "x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) ya"
then have f5: "x \<in> InfrastructureOne.agra G ya"
using a1 by meson
  have f6: "ya \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G}"
    using a4 a1 InfrastructureOne.nodes_def by blast
  { assume "x \<in> InfrastructureOne.agra G l"
    moreover
    { assume "\<exists>la. x \<in> InfrastructureOne.agra G l \<and> la = l \<and> x \<noteq> a"
      then have "(\<exists>la. x \<in> InfrastructureOne.agra G l \<and> la = l \<and> x \<noteq> a \<and> l' \<noteq> l) \<or> (\<exists>la lb. x \<in> InfrastructureOne.agra G la \<and> x \<in> InfrastructureOne.agra G l \<and> x \<in> InfrastructureOne.agra G l' \<and> lb = l \<and> la \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G} \<and> l' \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) ((InfrastructureOne.agra G) (l' := insert a (InfrastructureOne.agra G l'))) (InfrastructureOne.cgra G) (InfrastructureOne.lgra G) ((InfrastructureOne.egra G) (l' := insert (efids_cur (InfrastructureOne.cgra G a)) (InfrastructureOne.egra G l'))) (InfrastructureOne.kgra G)) \<or> (la, l) \<in> InfrastructureOne.gra (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) ((InfrastructureOne.agra G) (l' := insert a (InfrastructureOne.agra G l'))) (InfrastructureOne.cgra G) (InfrastructureOne.lgra G) ((InfrastructureOne.egra G) (l' := insert (efids_cur (InfrastructureOne.cgra G a)) (InfrastructureOne.egra G l'))) (InfrastructureOne.kgra G))} \<and> l \<in> {la. \<exists>lb. (la, lb) \<in> InfrastructureOne.gra (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) ((InfrastructureOne.agra G) (l := InfrastructureOne.agra G l - {a}, l' := insert a (InfrastructureOne.agra G l'))) (InfrastructureOne.cgra G) (InfrastructureOne.lgra G) ((InfrastructureOne.egra G) (l := InfrastructureOne.egra G l - {efids_cur (InfrastructureOne.cgra G a)}, l' := insert (efids_cur (InfrastructureOne.cgra G a)) (InfrastructureOne.egra G l'))) (InfrastructureOne.kgra G)) \<or> (lb, la) \<in> InfrastructureOne.gra (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) ((InfrastructureOne.agra G) (l := InfrastructureOne.agra G l - {a}, l' := insert a (InfrastructureOne.agra G l'))) (InfrastructureOne.cgra G) (InfrastructureOne.lgra G) ((InfrastructureOne.egra G) (l := InfrastructureOne.egra G l - {efids_cur (InfrastructureOne.cgra G a)}, l' := insert (efids_cur (InfrastructureOne.cgra G a)) (InfrastructureOne.egra G l'))) (InfrastructureOne.kgra G))} \<and> x \<noteq> a)"
        using a2 a1 InfrastructureOne.nodes_def by auto
      moreover
      { assume "\<exists>la lb. x \<in> InfrastructureOne.agra G la \<and> x \<in> InfrastructureOne.agra G l \<and> x \<in> InfrastructureOne.agra G l' \<and> lb = l \<and> la \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G} \<and> l' \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) ((InfrastructureOne.agra G) (l' := insert a (InfrastructureOne.agra G l'))) (InfrastructureOne.cgra G) (InfrastructureOne.lgra G) ((InfrastructureOne.egra G) (l' := insert (efids_cur (InfrastructureOne.cgra G a)) (InfrastructureOne.egra G l'))) (InfrastructureOne.kgra G)) \<or> (la, l) \<in> InfrastructureOne.gra (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) ((InfrastructureOne.agra G) (l' := insert a (InfrastructureOne.agra G l'))) (InfrastructureOne.cgra G) (InfrastructureOne.lgra G) ((InfrastructureOne.egra G) (l' := insert (efids_cur (InfrastructureOne.cgra G a)) (InfrastructureOne.egra G l'))) (InfrastructureOne.kgra G))} \<and> l \<in> {la. \<exists>lb. (la, lb) \<in> InfrastructureOne.gra (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) ((InfrastructureOne.agra G) (l := InfrastructureOne.agra G l - {a}, l' := insert a (InfrastructureOne.agra G l'))) (InfrastructureOne.cgra G) (InfrastructureOne.lgra G) ((InfrastructureOne.egra G) (l := InfrastructureOne.egra G l - {efids_cur (InfrastructureOne.cgra G a)}, l' := insert (efids_cur (InfrastructureOne.cgra G a)) (InfrastructureOne.egra G l'))) (InfrastructureOne.kgra G)) \<or> (lb, la) \<in> InfrastructureOne.gra (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) ((InfrastructureOne.agra G) (l := InfrastructureOne.agra G l - {a}, l' := insert a (InfrastructureOne.agra G l'))) (InfrastructureOne.cgra G) (InfrastructureOne.lgra G) ((InfrastructureOne.egra G) (l := InfrastructureOne.egra G l - {efids_cur (InfrastructureOne.cgra G a)}, l' := insert (efids_cur (InfrastructureOne.cgra G a)) (InfrastructureOne.egra G l'))) (InfrastructureOne.kgra G))} \<and> x \<noteq> a"
        then have "(a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
          using a1 InfrastructureOne.nodes_def by auto }
      moreover
      { assume "\<exists>la. x \<in> InfrastructureOne.agra G l \<and> la = l \<and> x \<noteq> a \<and> l' \<noteq> l"
        then have "(a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
          using a2 a1 InfrastructureOne.nodes_def by auto }
      ultimately have "(a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
        by fastforce }
    moreover
    { assume "x = a"
      moreover
      { assume "x = a \<and> a \<notin> InfrastructureOne.agra G l'"
        moreover
        { assume "a \<notin> InfrastructureOne.agra G l"
          then have "\<exists>la. x \<in> InfrastructureOne.agra G la \<and> la \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G} \<and> a \<notin> InfrastructureOne.agra G l"
            using f6 f5 by blast }
        ultimately have "(\<exists>la. x \<in> InfrastructureOne.agra G la \<and> la \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G} \<and> a \<notin> InfrastructureOne.agra G l) \<or> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
          using a3 a1 InfrastructureOne.nodes_def by fastforce }
      moreover
      { assume "a \<in> InfrastructureOne.agra G l'"
        then have "\<exists>l. x \<in> InfrastructureOne.agra G l \<and> a \<in> InfrastructureOne.agra G l' \<and> l \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G}"
          using f6 f5 by blast }
      ultimately have "(\<exists>la. x \<in> InfrastructureOne.agra G la \<and> la \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G} \<and> a \<notin> InfrastructureOne.agra G l) \<or> (\<exists>l. x \<in> InfrastructureOne.agra G l \<and> a \<in> InfrastructureOne.agra G l' \<and> l \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G}) \<or> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
        by fastforce }
    ultimately have "(\<exists>la. x \<in> InfrastructureOne.agra G la \<and> la \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G} \<and> a \<notin> InfrastructureOne.agra G l) \<or> (\<exists>l. x \<in> InfrastructureOne.agra G l \<and> a \<in> InfrastructureOne.agra G l' \<and> l \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G}) \<or> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
      by fastforce }
  moreover
  { assume "x \<notin> InfrastructureOne.agra G l"
    then have "ya \<noteq> l"
      using f5 by meson
    moreover
    { assume "ya \<noteq> l \<and> x \<notin> InfrastructureOne.agra G l'"
      then have "(\<exists>la. x \<in> InfrastructureOne.agra G la \<and> la \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G} \<and> a \<notin> InfrastructureOne.agra G l) \<or> (\<exists>l. x \<in> InfrastructureOne.agra G l \<and> a \<in> InfrastructureOne.agra G l' \<and> l \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G}) \<or> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
        using f6 f5 a1 InfrastructureOne.nodes_def by auto }
    ultimately have "(\<exists>la. x \<in> InfrastructureOne.agra G la \<and> la \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G} \<and> a \<notin> InfrastructureOne.agra G l) \<or> (\<exists>l. x \<in> InfrastructureOne.agra G l \<and> a \<in> InfrastructureOne.agra G l' \<and> l \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G}) \<or> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
      using a3 a1 InfrastructureOne.nodes_def by fastforce }
  ultimately have "(\<exists>la. x \<in> InfrastructureOne.agra G la \<and> la \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G} \<and> a \<notin> InfrastructureOne.agra G l) \<or> (\<exists>l. x \<in> InfrastructureOne.agra G l \<and> a \<in> InfrastructureOne.agra G l' \<and> l \<in> {l. \<exists>la. (l, la) \<in> InfrastructureOne.gra G \<or> (la, l) \<in> InfrastructureOne.gra G}) \<or> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
    by fastforce
  then show "(a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> ((a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow> (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) la)))) \<and> (\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I)) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l))"
    using a1 InfrastructureOne.nodes_def by auto
next show " \<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI I)) (InfrastructureOne.delta I) \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>InfrastructureOne.graphI I\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<Longrightarrow>
       \<exists>y. y \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<and>
           a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) y \<Longrightarrow>
       InfrastructureOne.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI I)) (InfrastructureOne.delta I) \<Longrightarrow>
       {x. \<exists>y. y \<in> InfrastructureOne.nodes (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI I)) \<and>
               x \<in> InfrastructureOne.agra (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI I)) y}
       \<subseteq> {x. \<exists>y. y \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<and>
                  x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) y}"

    apply (simp add: InfrastructureOne.enables_def move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
     apply (rule subsetI)
     apply (rule CollectI)
     apply (drule CollectD)
     apply (erule exE)+
    apply (erule conjE)+
  proof -
fix z :: InfrastructureOne.infrastructure and z' :: InfrastructureOne.infrastructure and G :: InfrastructureOne.igraph and I :: InfrastructureOne.infrastructure and a :: "char list" and l :: location and l' :: location and I' :: InfrastructureOne.infrastructure and x :: "char list" and y :: location and ya :: location
assume a1: "G = InfrastructureOne.graphI I"
  assume a2: "ya = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)"
assume a3: "l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I)"
assume a4: "l' \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I)"
assume a5: "a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) y"
  assume a6: "ya \<noteq> l \<longrightarrow> (ya = l' \<longrightarrow> l' \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and> (ya \<noteq> l' \<longrightarrow> ya \<in> InfrastructureOne.nodes (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I)) ((InfrastructureOne.agra (InfrastructureOne.graphI I)) (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}, l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I)) ((InfrastructureOne.egra (InfrastructureOne.graphI I)) (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l - {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}, l' := insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))) (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) ya)"
  assume a7: "y \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I)"
  have "ya = l' \<or> ya = l \<or> (\<exists>l. x \<in> InfrastructureOne.agra G l \<and> l \<in> InfrastructureOne.nodes G)"
    using a6 a1 InfrastructureOne.nodes_def by force
  then show "\<exists>l. l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<and> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l"
    using a7 a6 a5 a4 a3 a2 a1 by (metis (no_types))
next show "\<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
          (if a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and>
              a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l'
           then (InfrastructureOne.agra (InfrastructureOne.graphI I))
                (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a},
                 l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))
           else InfrastructureOne.agra (InfrastructureOne.graphI I))
          (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I))
          (if a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and>
              a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l'
           then (InfrastructureOne.egra (InfrastructureOne.graphI I))
                (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l -
                      {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)},
                 l' :=
                   insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))
                    (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))
           else InfrastructureOne.egra (InfrastructureOne.graphI I))
          (InfrastructureOne.kgra (InfrastructureOne.graphI I)))
        (InfrastructureOne.delta I) \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>InfrastructureOne.graphI I\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<Longrightarrow>
       \<exists>y. y \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<and>
           a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) y \<Longrightarrow>
       \<exists>x\<in>InfrastructureOne.delta I (InfrastructureOne.graphI I) l'. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a) \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
          (if a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and>
              a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l'
           then (InfrastructureOne.agra (InfrastructureOne.graphI I))
                (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a},
                 l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l'))
           else InfrastructureOne.agra (InfrastructureOne.graphI I))
          (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I))
          (if a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and>
              a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l'
           then (InfrastructureOne.egra (InfrastructureOne.graphI I))
                (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l -
                      {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)},
                 l' :=
                   insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))
                    (InfrastructureOne.egra (InfrastructureOne.graphI I) l'))
           else InfrastructureOne.egra (InfrastructureOne.graphI I))
          (InfrastructureOne.kgra (InfrastructureOne.graphI I)))
        (InfrastructureOne.delta I) \<Longrightarrow>
       (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>
        a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l') \<longrightarrow>
       (a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and>
        a \<notin> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow>
        {x. \<exists>y. (y = l \<longrightarrow>
                 (l = l' \<longrightarrow>
                  l' \<in> InfrastructureOne.nodes
                         (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
                           ((InfrastructureOne.agra (InfrastructureOne.graphI I))
                            (l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l')))
                           (InfrastructureOne.cgra (InfrastructureOne.graphI I))
                           (InfrastructureOne.lgra (InfrastructureOne.graphI I))
                           ((InfrastructureOne.egra (InfrastructureOne.graphI I))
                            (l' :=
                               insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))
                                (InfrastructureOne.egra (InfrastructureOne.graphI I) l')))
                           (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and>
                  (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and>
                 (l \<noteq> l' \<longrightarrow>
                  l \<in> InfrastructureOne.nodes
                        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
                          ((InfrastructureOne.agra (InfrastructureOne.graphI I))
                           (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a},
                            l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l')))
                          (InfrastructureOne.cgra (InfrastructureOne.graphI I))
                          (InfrastructureOne.lgra (InfrastructureOne.graphI I))
                          ((InfrastructureOne.egra (InfrastructureOne.graphI I))
                           (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l -
                                 {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)},
                            l' :=
                              insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))
                               (InfrastructureOne.egra (InfrastructureOne.graphI I) l')))
                          (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and>
                  x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<and> x \<noteq> a)) \<and>
                (y \<noteq> l \<longrightarrow>
                 (y = l' \<longrightarrow>
                  l' \<in> InfrastructureOne.nodes
                         (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
                           ((InfrastructureOne.agra (InfrastructureOne.graphI I))
                            (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a},
                             l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l')))
                           (InfrastructureOne.cgra (InfrastructureOne.graphI I))
                           (InfrastructureOne.lgra (InfrastructureOne.graphI I))
                           ((InfrastructureOne.egra (InfrastructureOne.graphI I))
                            (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l -
                                  {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)},
                             l' :=
                               insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))
                                (InfrastructureOne.egra (InfrastructureOne.graphI I) l')))
                           (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and>
                  (x = a \<or> x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l')) \<and>
                 (y \<noteq> l' \<longrightarrow>
                  y \<in> InfrastructureOne.nodes
                        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
                          ((InfrastructureOne.agra (InfrastructureOne.graphI I))
                           (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a},
                            l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l')))
                          (InfrastructureOne.cgra (InfrastructureOne.graphI I))
                          (InfrastructureOne.lgra (InfrastructureOne.graphI I))
                          ((InfrastructureOne.egra (InfrastructureOne.graphI I))
                           (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l -
                                 {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)},
                            l' :=
                              insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))
                               (InfrastructureOne.egra (InfrastructureOne.graphI I) l')))
                          (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and>
                  x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) y))}
        \<subseteq> {x. \<exists>y. y \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<and>
                   x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) y}) \<and>
       {x. \<exists>y. y \<in> InfrastructureOne.nodes
                     (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
                       (InfrastructureOne.agra (InfrastructureOne.graphI I))
                       (InfrastructureOne.cgra (InfrastructureOne.graphI I))
                       (InfrastructureOne.lgra (InfrastructureOne.graphI I))
                       (InfrastructureOne.egra (InfrastructureOne.graphI I))
                       (InfrastructureOne.kgra (InfrastructureOne.graphI I))) \<and>
               x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) y}
       \<subseteq> {x. \<exists>y. y \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<and>
                  x \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) y}"
    using InfrastructureOne.nodes_def by auto
qed
qed
next show "\<And>z z' G I a l I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       InfrastructureOne.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)
           (a := (InfrastructureOne.kgra G a)
              (l := {(x, y). x \<in> InfrastructureOne.agra G l \<and> y \<in> InfrastructureOne.egra G l}))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z')"
    by (simp add: InfrastructureOne.actors_graph_def InfrastructureOne.nodes_def)
next show "\<And>z z' G I a l I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureOne.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid a l G)
        (InfrastructureOne.delta I) \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z')"
    by (simp add: InfrastructureOne.actors_graph_def InfrastructureOne.nodes_def InfrastructureOne.put_graph_efid_def)
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
  apply (erule InfrastructureOne.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def put_graph_efid_def)+

lemma same_nodes: "(c, s) \<in> {(x::InfrastructureOne.infrastructure, y::InfrastructureOne.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> InfrastructureOne.nodes (graphI c) = InfrastructureOne.nodes (graphI s)"
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
    apply (rule delta_invariant)
  by assumption

(* anonymous actor invariant, i.e. we show that any efid that appears in a state, that is, either in  
  the egra component or in the kgra component, is in the range of an efidlist for some actor a
  in the set of actors of the infrastructure. Typical for invariants, we first show that the invariant 
  is preserved in a step, and this is then simply extrapolated by induction to any reachable I has the 
  property if it is reached from an initial I that already had that property.*)
lemma efids_list_eq[rule_format]: "(\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow> 
efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) =
efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))"

proof (clarify, frule same_actors0, frule same_nodes0, erule state_transition_in.cases)
  show "\<And>z z' G I aa l l' I'.
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes G \<Longrightarrow>
       aa \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
       InfrastructureOne.enables I l' (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a aa l l' (InfrastructureOne.graphI I)) (InfrastructureOne.delta I) \<Longrightarrow>
       efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) =
       efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)"
    using InfrastructureOne.cgra.simps InfrastructureOne.graphI.simps InfrastructureOne.move_graph_a_def by presburger
next show "\<And>z z' G I aa l I'.
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       InfrastructureOne.enables I l (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)
           (aa := (InfrastructureOne.kgra G aa)
              (l := {(x, y). x \<in> InfrastructureOne.agra G l \<and> y \<in> InfrastructureOne.egra G l}))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) =
       efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)"
    by force
next show "\<And>z z' G I aa l I'.
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureOne.enables I l (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid aa l G)
        (InfrastructureOne.delta I) \<Longrightarrow>
       efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) =
       efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a) "
    by (metis InfrastructureOne.cgra.simps InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def efidlist.exhaust efids_inc_ind.simps efids_list.simps fun_upd_apply)
qed

lemma efids_list_eq0: "\<And> z z'. (z \<rightarrow>\<^sub>n z') \<Longrightarrow>
\<forall> a. efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) =
efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)"
  by (simp add: efids_list_eq)


lemma efid_in_range_invariantO: "(\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow> 
         (\<forall> l \<in> nodes (graphI z).
         (\<forall> e \<in> (egra (InfrastructureOne.graphI z) l).
         (\<exists> a \<in> actors_graph (graphI z). e \<in> range (efids_list (InfrastructureOne.cgra (graphI z) a)))))
          \<longrightarrow>  (\<forall> l \<in> nodes (graphI z').
         (\<forall> e \<in> (egra (InfrastructureOne.graphI z') l). 
         (\<exists> a \<in> actors_graph (graphI z'). e \<in> range (efids_list (InfrastructureOne.cgra (graphI z') a))))))"
proof (clarify, frule same_actors0, frule same_nodes0, frule efids_list_eq0, erule state_transition_in.cases)
  show "\<And>z z' l e G I a la l' I'.
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
             \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI z') l \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureOne.nodes G \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes G \<Longrightarrow>
       a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
       InfrastructureOne.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a a la l' (InfrastructureOne.graphI I)) (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z').
          e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))"
    apply (case_tac "a \<in> ((agra (InfrastructureOne.graphI I)) la) &  a \<notin> ((agra (InfrastructureOne.graphI I)) l')")
     prefer 2
     apply (simp add: move_graph_a_def)+
    apply (simp add: atI_def nodes_def)
    by (metis (mono_tags, lifting) Diff_iff UNIV_I efidlist.exhaust efids_cur.simps efids_list.simps fun_upd_apply image_eqI insertE)
     (* for Isabelle 2021-1 ...(mono_tags, opaque_lifting)... *)
next show " \<And>z z' l e G I a la I'.
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
             \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI z') l \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureOne.nodes G \<Longrightarrow>
       InfrastructureOne.enables I la (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)
           (a := (InfrastructureOne.kgra G a)
              (la := {(x, y). x \<in> InfrastructureOne.agra G la \<and> y \<in> InfrastructureOne.egra G la}))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z').
          e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))"
    by simp
next show "\<And>z z' l e G I a la I'.
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
             \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI z') l \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       \<forall>a. efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) =
           efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureOne.enables I la (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid a la G)
        (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z').
          e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))"
    by (smt (z3) Diff_iff InfrastructureOne.actors_graph_def InfrastructureOne.atI_def InfrastructureOne.egra.simps InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def UNIV_I efidlist.exhaust efids_cur.simps efids_inc_ind.simps efids_list.simps fun_upd_apply image_eqI insert_iff mem_Collect_eq)
qed

(* variation for applicability*)
lemma efid_in_range_invariantOa: "(z \<rightarrow>\<^sub>n z') \<Longrightarrow> 
         (\<forall> l \<in> nodes (graphI z).
         (\<forall> e \<in> (egra (InfrastructureOne.graphI z) l).
         (\<exists> a \<in> actors_graph (graphI z). e \<in> range (efids_list (InfrastructureOne.cgra (graphI z) a)))))
          \<Longrightarrow>  (\<forall> l \<in> nodes (graphI z').
         (\<forall> e \<in> (egra (InfrastructureOne.graphI z') l). 
         (\<exists> a \<in> actors_graph (graphI z'). e \<in> range (efids_list (InfrastructureOne.cgra (graphI z') a)))))"
  using efid_in_range_invariantO by presburger

(*
lemma efid_in_range_invariant: "(\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
         (l \<in> nodes (graphI z) \<longrightarrow>
         e \<in> (egra (InfrastructureOne.graphI z) l) \<longrightarrow> 
         (\<exists> a \<in> actors_graph (graphI z). e \<in> range (efids_list (InfrastructureOne.cgra (graphI z) a))))
          \<longrightarrow>  (l \<in> nodes (graphI z') \<longrightarrow>
         e \<in> (egra (InfrastructureOne.graphI z') l) \<longrightarrow> 
         (\<exists> a \<in> actors_graph (graphI z'). e \<in> range (efids_list (InfrastructureOne.cgra (graphI z') a)))))"
  sorry
*)

lemma efids_in_range_invariantOO[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
        \<Longrightarrow> (\<forall> l \<in> nodes (graphI I).
            \<forall> e \<in> (egra (InfrastructureOne.graphI I) l).
         \<exists> a \<in> actors_graph (graphI I). e \<in> range (efids_list (InfrastructureOne.cgra (graphI I) a)))
       \<Longrightarrow> (\<forall> l \<in> nodes (graphI y).
           \<forall> e \<in> (egra (InfrastructureOne.graphI y) l).
         \<exists> a \<in> actors_graph (graphI y). e \<in> range (efids_list (InfrastructureOne.cgra (graphI y) a)))"
proof (erule rtrancl_induct)
  show "\<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
       \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
          \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
             e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
    \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
       \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
          \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
             e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))"
    by blast
next show "\<And>y z. \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
              \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
                 \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                    e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI y).
              \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI y) l.
                 \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI y).
                    e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI y) a)) \<Longrightarrow>
           \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
              \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
                 \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                    e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) "
    using efid_in_range_invariantO by auto
qed

(*
lemma efid_in_range_invariantOOO: "(\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow> 
         (\<forall> l \<in> nodes (graphI z).
         (\<forall> e \<in> (egra (InfrastructureOne.graphI z) l).
         (\<exists> a \<in> agra (graphI z) l. e \<in> range (efids_list (InfrastructureOne.cgra (graphI z) a)))))
          \<longrightarrow>  (\<forall> l \<in> nodes (graphI z').
         (\<forall> e \<in> (egra (InfrastructureOne.graphI z') l). 
         (\<exists> a \<in> agra (graphI z') l. e \<in> range (efids_list (InfrastructureOne.cgra (graphI z') a))))))"
    sorry

proof (clarify, frule same_actors0, frule same_nodes0, frule efids_list_eq0, erule state_transition_in.cases)
  show "\<And>z z' l e G I a la l' I'.
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
             \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI z) l.
                e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI z') l \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       \<forall>a. efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) =
           efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureOne.nodes G \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes G \<Longrightarrow>
       a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
       InfrastructureOne.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a a la l' (InfrastructureOne.graphI I)) (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI z') l.
          e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))"
    apply (case_tac "a \<in> ((agra (InfrastructureOne.graphI I)) la) &  a \<notin> ((agra (InfrastructureOne.graphI I)) l')")
     prefer 2
     apply (simp add: move_graph_a_def)+
    apply (rule conjI)
     apply (rule impI)+
     apply (rule conjI)
    apply (rule impI)+
      apply fastforce
     apply (rule impI)
*)

(*
lemma efids_in_range_invariantOOOO[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
        \<Longrightarrow> (\<forall> l \<in> nodes (graphI I).
            \<forall> e \<in> (egra (InfrastructureOne.graphI I) l).
         \<exists> a \<in> agra (graphI I) l. e \<in> range (efids_list (InfrastructureOne.cgra (graphI I) a)))
       \<Longrightarrow> (\<forall> l \<in> nodes (graphI y).
           \<forall> e \<in> (egra (InfrastructureOne.graphI y) l).
         \<exists> a \<in> agra (graphI y) l. e \<in> range (efids_list (InfrastructureOne.cgra (graphI y) a)))"
  sorry
*)

lemma anonymous_actor_eq: "(z \<rightarrow>\<^sub>n z') \<Longrightarrow> 
InfrastructureOne.actors_graph (InfrastructureOne.graphI z) \<noteq> {} \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI z). inj (efids_list (InfrastructureOne.cgra (graphI z) a))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI z). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<inter> 
      (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a')))) = {}))) \<Longrightarrow>
    e \<in> (\<Union> a \<in> actors_graph (InfrastructureOne.graphI z). 
            range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)))
\<Longrightarrow>    anonymous_actor z e = anonymous_actor z' e"
  by (smt (verit, ccfv_threshold) InfrastructureOne.actors_graph_def InfrastructureOne.same_actors0 UN_iff anonymous_actor_def1b efids_list_eq0 mem_Collect_eq)




(* This version is too special because ot the missing quantification 
lemma anonymous_actor: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
        \<Longrightarrow> l \<in> nodes (graphI I) \<Longrightarrow>
         e \<in> (egra (InfrastructureOne.graphI I) l) \<Longrightarrow> 
         \<exists> a \<in> actors_graph (graphI I). e \<in> range (efids_list (InfrastructureOne.cgra (graphI I) a))
       \<Longrightarrow> l \<in> nodes (graphI y) \<Longrightarrow>
         e \<in> (egra (InfrastructureOne.graphI y) l) \<Longrightarrow> 
         \<exists> a \<in> actors_graph (graphI y). e \<in> range (efids_list (InfrastructureOne.cgra (graphI y) a))"
proof (erule rtrancl_induct)
  show " l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<Longrightarrow>
    e \<in> InfrastructureOne.egra (InfrastructureOne.graphI I) l \<Longrightarrow>
    \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
       e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
    l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI y) \<Longrightarrow>
    e \<in> InfrastructureOne.egra (InfrastructureOne.graphI y) l \<Longrightarrow>
    \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
       e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))"
    by blast
next show "\<And>ya z.
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI I) l \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
          e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI y) \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI y) l \<Longrightarrow>
       (I, ya) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (ya, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI ya).
          e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI ya) a)) \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
          e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) "
    using InfrastructureOne.same_actors efids_list_eq by auto
qed
*)

(* Same as for egra also for kgra *)
lemma efid_kgra_in_range_invariantO: 
"\<forall> (z :: InfrastructureOne.infrastructure)(z' ::InfrastructureOne.infrastructure). (z \<rightarrow>\<^sub>n z') \<longrightarrow> 
         (\<forall> l \<in> nodes (graphI z).
         (\<forall> e \<in> (egra (InfrastructureOne.graphI z) l).
         (\<exists> a \<in> actors_graph (graphI z). e \<in> range (efids_list (InfrastructureOne.cgra (graphI z) a))))) \<longrightarrow>
         (\<forall> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z). 
         (\<forall> h \<in> InfrastructureOne.actors_graph(InfrastructureOne.graphI z).
         (\<forall> e \<in> (snd`((InfrastructureOne.kgra (InfrastructureOne.graphI z) h l))).
         (\<exists> a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI z). 
           e \<in> range (InfrastructureOne.efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))))))
          \<longrightarrow>  
         (\<forall> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z'). 
         (\<forall> h' \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI z').
         (\<forall> e \<in> (snd `((InfrastructureOne.kgra (InfrastructureOne.graphI z') h' l))). 
         (\<exists> a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI z'). 
              e \<in> range (InfrastructureOne.efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))))))"
proof (clarify, frule same_actors0, erule state_transition_in.cases)
  show "\<And>z z' l h' e a b G I aa la l' I'.
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>h\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
             \<forall>e\<in>snd ` InfrastructureOne.kgra (InfrastructureOne.graphI z) h l.
                \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                   e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       h' \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       (a, b) \<in> InfrastructureOne.kgra (InfrastructureOne.graphI z') h' l \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureOne.nodes G \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes G \<Longrightarrow>
       aa \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
       InfrastructureOne.enables I l' (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a aa la l' (InfrastructureOne.graphI I)) (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>aa\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z').
          snd (a, b) \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') aa))"
    apply (simp add: move_graph_a_def)
    by (smt (z3) Collect_cong Diff_iff InfrastructureOne.actors_graph_def InfrastructureOne.agra.simps InfrastructureOne.gra.simps InfrastructureOne.nodes_def fun_upd_apply insert_iff singletonD snd_conv)
next show "\<And>z z' l h' e a b G I aa la I'.
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>h\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
             \<forall>e\<in>snd ` InfrastructureOne.kgra (InfrastructureOne.graphI z) h l.
                \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                   e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       h' \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       (a, b) \<in> InfrastructureOne.kgra (InfrastructureOne.graphI z') h' l \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureOne.enables I la (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid aa la G)
        (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>aa\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z').
          snd (a, b) \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') aa)) "
    apply (simp add: put_graph_efid_def)
    by (metis (no_types, opaque_lifting) InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def InfrastructureOne.same_actors0 InfrastructureOne.same_nodes0 InfrastructureOne.state_transition_in.put efidlist.exhaust efids_inc_ind.simps efids_list.simps snd_conv)
next show "\<And>z z' l h' e a b G I aa la I'.
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
             \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>h\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
             \<forall>e\<in>snd ` InfrastructureOne.kgra (InfrastructureOne.graphI z) h l.
                \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                   e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       h' \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       (a, b) \<in> InfrastructureOne.kgra (InfrastructureOne.graphI z') h' l \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureOne.nodes G \<Longrightarrow>
       InfrastructureOne.enables I la (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)
           (aa := (InfrastructureOne.kgra G aa)
              (la := {(x, y). x \<in> InfrastructureOne.agra G la \<and> y \<in> InfrastructureOne.egra G la}))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>aa\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z').
          snd (a, b) \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') aa))"
    apply (subgoal_tac " \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z').
          \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z') l.
             \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z').
                e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))")
     prefer 2
    using InfrastructureOne.nodes_def apply force
    apply (case_tac "l = la")
     apply (case_tac "h' = aa")
      apply fastforce
     apply (subgoal_tac "(a, b) \<in> InfrastructureOne.kgra (InfrastructureOne.graphI (InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)))
        (InfrastructureOne.delta I))) h' l")
      apply (subgoal_tac "(a, b) \<in> InfrastructureOne.kgra (InfrastructureOne.graphI z) h' l ")
    prefer 2
       apply (metis InfrastructureOne.graphI.simps InfrastructureOne.kgra.simps)
    apply (rotate_tac 1)
      apply (drule_tac x = l in bspec)
       apply simp
      apply (rotate_tac -1)
      apply (drule_tac x = h' in bspec)
       apply simp
      apply (rotate_tac -1)
      apply (drule_tac x = b in bspec)
    apply (metis image_iff snd_conv)
      apply simp
     apply simp
(* *)
      apply (subgoal_tac "(a, b) \<in> InfrastructureOne.kgra (InfrastructureOne.graphI (InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)))
        (InfrastructureOne.delta I))) h' l")
      apply (subgoal_tac "(a, b) \<in> InfrastructureOne.kgra (InfrastructureOne.graphI z) h' l ")
    prefer 2
       apply (metis InfrastructureOne.graphI.simps InfrastructureOne.kgra.simps)
    apply (rotate_tac 1)
      apply (drule_tac x = l in bspec)
    apply (simp add: InfrastructureOne.nodes_def)
      apply (rotate_tac -1)
      apply (rotate_tac -1)
      apply (drule_tac x = h' in bspec)
       apply simp
      apply (rotate_tac -1)
      apply (drule_tac x = b in bspec)
    apply (metis image_iff snd_conv)
      apply simp
    by (metis (no_types, lifting) InfrastructureOne.graphI.simps InfrastructureOne.kgra.simps fun_upd_apply)
qed

lemma efid_kgra_in_range_invariantOO[rule_format]: 
     "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
 \<Longrightarrow>  (\<forall> l \<in> nodes (graphI I).
         (\<forall> e \<in> (egra (InfrastructureOne.graphI I) l).
         (\<exists> a \<in> actors_graph (graphI I). e \<in> range (efids_list (InfrastructureOne.cgra (graphI I) a)))))
 \<Longrightarrow>  (\<forall> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I). 
         (\<forall> h \<in> InfrastructureOne.actors_graph(InfrastructureOne.graphI I).
         (\<forall> e \<in> (snd`((InfrastructureOne.kgra (InfrastructureOne.graphI I) h l))).
         (\<exists> a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I). 
           e \<in> range (InfrastructureOne.efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))))))
          \<Longrightarrow> 
         (\<forall> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI y). 
         (\<forall> h' \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI y).
         (\<forall> e \<in> (snd `((InfrastructureOne.kgra (InfrastructureOne.graphI y) h' l))). 
         (\<exists> a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI y). 
              e \<in> range (InfrastructureOne.efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI y) a))))))"
proof (erule rtrancl_induct)
  show " \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
       \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
          \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
             e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
    \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
       \<forall>h\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
          \<forall>e\<in>snd ` InfrastructureOne.kgra (InfrastructureOne.graphI I) h l.
             \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
    \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
       \<forall>h'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
          \<forall>e\<in>snd ` InfrastructureOne.kgra (InfrastructureOne.graphI I) h' l.
             \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))"
    by blast
next show " \<And>y z. \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
              \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
                 \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                    e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
           \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
              \<forall>h\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                 \<forall>e\<in>snd ` InfrastructureOne.kgra (InfrastructureOne.graphI I) h l.
                    \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                       e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI y).
              \<forall>h'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI y).
                 \<forall>e\<in>snd ` InfrastructureOne.kgra (InfrastructureOne.graphI y) h' l.
                    \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI y).
                       e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI y) a)) \<Longrightarrow>
           \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
              \<forall>h'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                 \<forall>e\<in>snd ` InfrastructureOne.kgra (InfrastructureOne.graphI z) h' l.
                    \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                       e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) "
    using efid_kgra_in_range_invariantO efids_in_range_invariantOO by auto
qed



lemma efids_root_efids_inc_lem: "efids_root (efids_inc_ind el) = efids_root el"
  by (case_tac el, simp add: efids_inc_ind_def efids_root_def)

text \<open> similar to same_nodes we need to prove invariant for reachable states:
       xa \<noteq> a \<Longrightarrow>
       efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) xa) \<noteq>
       efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) a) \<close>
(* efids invariants *)
lemma eroots_inj_inv0: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>  
(inj(\<lambda> x. efids_root(InfrastructureOne.cgra (InfrastructureOne.graphI z) x)) \<longrightarrow> 
inj(\<lambda> x. efids_root(InfrastructureOne.cgra (InfrastructureOne.graphI z') x)))))"
    apply clarify
  apply (erule InfrastructureOne.state_transition_in.cases)
  apply (simp add: InfrastructureOne.move_graph_a_def)
  apply simp
  by (smt InfrastructureOne.cgra.simps InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def efids_root_efids_inc_lem fun_upd_apply inj_on_cong)

lemma eroots_inj_inv[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
\<Longrightarrow> (inj(\<lambda> x. efids_root(InfrastructureOne.cgra (InfrastructureOne.graphI I) x)) \<longrightarrow> 
     inj(\<lambda> x. efids_root(InfrastructureOne.cgra (InfrastructureOne.graphI y) x)))"
proof (erule rtrancl_induct)
  show "inj (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) x)) \<longrightarrow>
    inj (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))" by simp
next show "\<And>y z. (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           inj (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) x)) \<longrightarrow>
           inj (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI y) x)) \<Longrightarrow>
           inj (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) x)) \<longrightarrow>
           inj (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI z) x)) "
    using eroots_inj_inv0 by auto
qed

lemma eroots_inj_on_inv0: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>  
(inj_on(\<lambda> x. efids_root(InfrastructureOne.cgra (InfrastructureOne.graphI z) x)) 
           (actors_graph (InfrastructureOne.graphI z)) \<longrightarrow> 
     inj_on(\<lambda> x. efids_root(InfrastructureOne.cgra (InfrastructureOne.graphI z') x))
           (actors_graph (InfrastructureOne.graphI z')))))"
    apply clarify
  apply (erule InfrastructureOne.state_transition_in.cases)
    apply (simp add: InfrastructureOne.move_graph_a_def actors_graph_def inj_on_def
                    InfrastructureOne.gra.simps InfrastructureOne.nodes_def)
    apply (erule exE)+
    apply (rule impI)+
  apply (rule allI)
    apply (rule impI)+
    apply (rule allI)
  apply (rule impI)+
    apply (erule exE)+
    apply (erule conjE)+
    apply (erule exE)+
(* update to Isabelle 2021 solved remaining subgoals automatically (sledgehammer) *)
  apply metis
   apply (simp add: InfrastructureOne.actors_graph_def InfrastructureOne.nodes_def)
  by (smt (z3) InfrastructureOne.cgra.simps InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def InfrastructureOne.same_actors0 InfrastructureOne.state_transition_in.put efids_root_efids_inc_lem fun_upd_apply inj_on_def)

lemma eroots_inj_on_inv[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
\<Longrightarrow> (inj_on(\<lambda> x. efids_root(InfrastructureOne.cgra (InfrastructureOne.graphI I) x)) 
           (actors_graph (InfrastructureOne.graphI I)) \<longrightarrow> 
     inj_on(\<lambda> x. efids_root(InfrastructureOne.cgra (InfrastructureOne.graphI y) x))
           (actors_graph (InfrastructureOne.graphI y)))"
proof (erule rtrancl_induct)
show "inj_on (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
     (InfrastructureOne.actors_graph (InfrastructureOne.graphI I)) \<longrightarrow>
    inj_on (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
     (InfrastructureOne.actors_graph (InfrastructureOne.graphI I))"
  by simp
next show "\<And>y z. (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           inj_on (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
            (InfrastructureOne.actors_graph (InfrastructureOne.graphI I)) \<longrightarrow>
           inj_on (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI y) x))
            (InfrastructureOne.actors_graph (InfrastructureOne.graphI y)) \<Longrightarrow>
           inj_on (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
            (InfrastructureOne.actors_graph (InfrastructureOne.graphI I)) \<longrightarrow>
           inj_on (\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI z) x))
            (InfrastructureOne.actors_graph (InfrastructureOne.graphI z))"
    by (simp add: eroots_inj_on_inv0)
qed

(* *)
lemma efids_list_disjoint: "(\<forall> (z :: InfrastructureOne.infrastructure). (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI z). a \<noteq> a' \<longrightarrow> 
(range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<inter> 
 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a'))) = {}))
\<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI z'). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI z'). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)) \<inter> 
 (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a')))) = {})))
))"
    apply clarify
  apply (erule InfrastructureOne.state_transition_in.cases)
  apply (smt (verit, ccfv_SIG) InfrastructureOne.cgra.simps InfrastructureOne.graphI.simps InfrastructureOne.move_graph_a_def InfrastructureOne.same_actors0 InfrastructureOne.state_transition_in.move)
   apply (simp add: InfrastructureOne.actors_graph_def InfrastructureOne.nodes_def)
  apply (simp add: put_graph_efid_def)
  by (metis InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def InfrastructureOne.same_actors0 InfrastructureOne.state_transition_in.put efidlist.exhaust efids_inc_ind.simps efids_list.simps)


(* efids_cur inj_on*)
lemma efids_cur_in_efids_listO: "a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
           efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)
         \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))"
  apply (case_tac "(InfrastructureOne.cgra (InfrastructureOne.graphI I) a)")
  by simp


lemma efids_cur_in_efids_list: "a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
           efids_cur (efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))
         \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))"
  apply (case_tac "(InfrastructureOne.cgra (InfrastructureOne.graphI I) a)")
  by simp

lemma inj_on_put_preserve0: "\<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
          \<forall>a'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
             a \<noteq> a' \<longrightarrow>
             range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter>
             range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')) =
             {} \<Longrightarrow>
             \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
             efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
             inj_on (\<lambda>x. efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
                    (InfrastructureOne.actors_graph (InfrastructureOne.graphI I)) \<Longrightarrow>
            a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
              inj_on ((\<lambda>x. efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
                      (a:= efids_cur (efids_inc_ind ((InfrastructureOne.cgra (InfrastructureOne.graphI I) a)))))
        (InfrastructureOne.actors_graph (InfrastructureOne.graphI I))"
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
   apply (subgoal_tac "efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) x) \<in>
                       range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))")
   apply (subgoal_tac "efids_cur (efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<in>
                     range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))")
    apply fastforce
  apply (simp add: efids_list_def)
   prefer 2
  apply (case_tac "InfrastructureOne.cgra (InfrastructureOne.graphI I) x")
  apply simp
  by (metis efidlist.exhaust efidlist.simps(3) efids_cur_in_efids_list efids_list.simps)


lemma inj_on_put_preserve: "\<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
          \<forall>a'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
             a \<noteq> a' \<longrightarrow>
             range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter>
             range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')) =
             {} \<Longrightarrow>
       \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
             efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a) \<noteq>
          efids_cur(efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
       inj_on (\<lambda>x. efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
        (InfrastructureOne.actors_graph (InfrastructureOne.graphI I)) \<Longrightarrow>
      inj_on (\<lambda>x. efids_cur
              (if x = a then efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)
               else InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
        (InfrastructureOne.actors_graph (InfrastructureOne.graphI I))"
  by (smt (verit, ccfv_SIG) fun_upd_apply inj_on_cong inj_on_put_preserve0)




lemma efids_cur_inj_on_inv0[rule_format]: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a')))) = {}))) \<longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). 
      efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))) \<longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureOne.cgra (InfrastructureOne.graphI z) x)) 
           (actors_graph (InfrastructureOne.graphI z)) \<longrightarrow> 
     inj_on(\<lambda> x. efids_cur(InfrastructureOne.cgra (InfrastructureOne.graphI z') x))
           (actors_graph (InfrastructureOne.graphI z')))))"
    apply clarify
  apply (erule InfrastructureOne.state_transition_in.cases)
    apply (simp add: InfrastructureOne.move_graph_a_def actors_graph_def inj_on_def
                    InfrastructureOne.gra.simps InfrastructureOne.nodes_def)
    apply (erule exE)+
    apply (rule impI)+
  apply (rule allI)
    apply (rule impI)+
    apply (rule allI)
  apply (rule impI)+
    apply (erule exE)+
    apply (erule conjE)+
    apply (erule exE)+
(* update to Isabelle 2021 solved remaining subgoals automatically (sledgehammer) *)
    apply metis
(* get *)
  using InfrastructureOne.same_actors0 InfrastructureOne.state_transition_in.get apply fastforce
(* put *)
  by (smt (z3) InfrastructureOne.cgra.simps InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def InfrastructureOne.same_actors0 InfrastructureOne.state_transition_in.put fun_upd_apply inj_on_cong inj_on_put_preserve0)


(* additional invariants for applying/generalizing efids_cur_inj_on_inv0*)
lemma ran_efidslist_disjoint:
"(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI z). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<inter> 
 (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a')))) = {})))
\<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI z'). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI z'). a \<noteq> a' \<longrightarrow> 
((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)) \<inter> 
 (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a')))) = {})))
))"
  by (rule efids_list_disjoint)

lemma ran_efids_list_disjoint_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI I). a \<noteq> a' \<longrightarrow>
((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter> 
 (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')))) = {}))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI y). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI y). a \<noteq> a' \<longrightarrow>
((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI y) a)) \<inter> 
 (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI y) a')))) = {})))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
              \<forall>a'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')) =
                 {} \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI y).
              \<forall>a'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI y).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI y) a)) \<inter>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI y) a')) =
                 {} \<Longrightarrow>
           \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
              \<forall>a'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<inter>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a')) =
                 {}"
    by (simp add: ran_efidslist_disjoint)
qed


(* injectivity of efids_list is preserved and implies 
 (\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). 
      efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))) 
*)

lemma efids_list_inj: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). 
      inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<longrightarrow>
       inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)))))"

proof (clarify, erule InfrastructureOne.state_transition_in.cases)
  show "\<And>z z' a G I aa l l' I'.
       a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI z) \<Longrightarrow>
       inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes G \<Longrightarrow>
       aa \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
       InfrastructureOne.enables I l' (Actor aa) move \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a aa l l' (InfrastructureOne.graphI I)) (InfrastructureOne.delta I) \<Longrightarrow>
       inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))"
    using InfrastructureOne.move_graph_a_def by force
next show "\<And>z z' a G I aa l I'.
       a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI z) \<Longrightarrow>
       inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       InfrastructureOne.enables I l (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)
           (aa := (InfrastructureOne.kgra G aa)
              (l := {(x, y). x \<in> InfrastructureOne.agra G l \<and> y \<in> InfrastructureOne.egra G l}))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))"
    by simp
next show "\<And>z z' a G I aa l I'.
       a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI z) \<Longrightarrow>
       inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureOne.enables I l (Actor aa) put \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid aa l G)
        (InfrastructureOne.delta I) \<Longrightarrow>
       inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z') a))"
    by (metis InfrastructureOne.cgra.simps InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def efidlist.exhaust efids_inc_ind.simps efids_list.simps fun_upd_apply)
qed


lemma efids_list_inj_refl: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
a \<in> actors_graph(InfrastructureOne.graphI I) \<Longrightarrow>
inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI y) a))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
           inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI y) a)) \<Longrightarrow>
           inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))"
    by (simp add: InfrastructureOne.same_actors efids_list_inj)
qed

lemma efids_list_inj_imp_inc_ind_not_eq[rule_format]: " (\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). 
 inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<longrightarrow>
      efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)))"
proof (clarify, simp add: efids_inc_ind_def efids_cur_def efids_list_def, case_tac "InfrastructureOne.graphI z", simp)
  show "\<And>a x1 x2 x3 x4 x5 x6.
       a \<in> InfrastructureOne.actors_graph (InfrastructureOne.igraph.Lgraph x1 x2 x3 x4 x5 x6) \<Longrightarrow>
       inj (rec_efidlist (\<lambda>e n ef. ef) (x3 a)) \<Longrightarrow>
       rec_efidlist (\<lambda>e n ef. ef n) (x3 a) = rec_efidlist (\<lambda>e n ef. ef n) (rec_efidlist (\<lambda>e n. Efids e (Suc n)) (x3 a)) \<Longrightarrow>
       InfrastructureOne.graphI z = InfrastructureOne.igraph.Lgraph x1 x2 x3 x4 x5 x6 \<Longrightarrow> False"
    by (smt (z3) efidlist.exhaust efidlist.rec n_not_Suc_n the_inv_f_f)
qed


lemma efids_cur_inj_on_inv: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI I). a \<noteq> a' \<longrightarrow>
((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter> 
 (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')))) = {}))) \<Longrightarrow>
 \<forall> a \<in> actors_graph(InfrastructureOne.graphI I). 
     inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureOne.cgra (InfrastructureOne.graphI I) x)) 
           (actors_graph (InfrastructureOne.graphI I))) \<Longrightarrow>
(inj_on(\<lambda> x. efids_cur(InfrastructureOne.cgra (InfrastructureOne.graphI y) x)) 
           (actors_graph (InfrastructureOne.graphI y)))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
              \<forall>a'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')) =
                 {} \<Longrightarrow>
           \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
              inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
           inj_on (\<lambda>x. efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
            (InfrastructureOne.actors_graph (InfrastructureOne.graphI I)) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           inj_on (\<lambda>x. efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI y) x))
            (InfrastructureOne.actors_graph (InfrastructureOne.graphI y)) \<Longrightarrow>
           inj_on (\<lambda>x. efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) x))
            (InfrastructureOne.actors_graph (InfrastructureOne.graphI z))"
    apply (rule_tac z = y in efids_cur_inj_on_inv0, simp)
      apply (simp add: ran_efids_list_disjoint_refl)
    apply (rule efids_list_inj_imp_inc_ind_not_eq, assumption)
    apply (rule efids_list_inj_refl, simp)
    using InfrastructureOne.same_actors apply presburger
     apply (metis InfrastructureOne.same_actors)
    by blast
qed

(* agra \<longrightarrow> egra invariants *) 
lemma actor_unique_loc_lem00[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l' \<longrightarrow> l = l')) 
        \<longrightarrow> (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z') \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z') l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z') l' \<longrightarrow> l = l'))"
  apply (rule allI)+
  apply (rule impI)+
  apply (erule InfrastructureOne.state_transition_in.cases)
    apply (simp add: move_graph_a_def)
  apply auto[1]
  using InfrastructureOne.agra.simps InfrastructureOne.graphI.simps apply presburger
  using InfrastructureOne.agra.simps InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def by presburger



lemma actor_unique_loc_lem0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  (\<forall> l'. l' \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l \<longrightarrow> 
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l' \<longrightarrow> l = l'))) 
        \<longrightarrow> (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z') \<longrightarrow>  (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z') l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z') l' \<longrightarrow> l = l')))"
  apply (rule allI)+
  apply (rule impI)+
  apply (erule InfrastructureOne.state_transition_in.cases)
    apply (simp add: move_graph_a_def)
  using InfrastructureOne.atI_def apply force
  using InfrastructureOne.agra.simps InfrastructureOne.graphI.simps apply presburger
  using InfrastructureOne.agra.simps InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def by presburger
thm actor_unique_loc_lem0

lemma actor_unique_loc_lem0a: "z \<rightarrow>\<^sub>n z' \<Longrightarrow>  nodes (graphI z) = nodes (graphI z') \<Longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l' \<longrightarrow> l = l'))
        \<Longrightarrow> l \<in> nodes (graphI z') \<Longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z') l \<Longrightarrow> 
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z') l' \<Longrightarrow> l = l'"
  using actor_unique_loc_lem00 by presburger


lemma actor_unique_loc_lem[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
         (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI y) \<longrightarrow> 
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI y) l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI y) l' \<longrightarrow> l = l'))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a l l'.
              l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI y) \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI y) l \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI y) l' \<longrightarrow> l = l' \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z) \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI z) l \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI z) l' \<longrightarrow> l = l'"
    by (metis CollectD InfrastructureOne.same_nodes actor_unique_loc_lem0a case_prodD rtrancl.rtrancl_into_rtrancl)
qed

lemma isthere_lem0: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
           (inj_on(\<lambda> x. efids_cur(InfrastructureOne.cgra (InfrastructureOne.graphI z) x)) 
                     (actors_graph (InfrastructureOne.graphI z))) \<longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). 
      efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))) \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureOne.cgra (graphI z) a)) \<in> egra (graphI z) l)) 
        \<longrightarrow> (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  a \<in>  agra (graphI z') l' \<longrightarrow>
          efids_cur ((InfrastructureOne.cgra (graphI z') a)) \<in> egra (graphI z') l'))"
  apply (rule allI)+
  apply (rule impI)
  apply (rule InfrastructureOne.state_transition_in.cases, assumption)
    apply (simp add: move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
     apply (rule allI)
      apply (rule impI)+
      apply (erule conjE)+
  apply (metis (no_types, lifting) InfrastructureOne.actors_graph_def inj_on_contraD mem_Collect_eq)
  apply (rule impI)+
    apply fastforce
(* get *)
      apply (rule impI)+
  using InfrastructureOne.agra.simps InfrastructureOne.cgra.simps InfrastructureOne.egra.simps InfrastructureOne.graphI.simps apply presburger
(* put *)
  apply (rule impI)+
  apply (rule allI)+
  apply (rule impI)+
  apply simp
  apply (simp add: put_graph_efid_def)
  apply (rule conjI)
  prefer 2
  apply (metis (mono_tags, lifting) InfrastructureOne.actors_graph_def InfrastructureOne.atI_def inj_on_def mem_Collect_eq)
  apply (rule impI)+
  apply (subgoal_tac "l' = l")
   apply simp
  apply (rule_tac z = z and z' = z' and a = a in actor_unique_loc_lem0a)
       prefer 5
  apply simp
  apply force
  apply (meson InfrastructureOne.same_nodes0)
  apply presburger
  apply (metis InfrastructureOne.same_nodes0)
by (simp add: atI_def)

lemma isthere_lem0a: "z \<rightarrow>\<^sub>n z' \<Longrightarrow>  nodes (graphI z) = nodes (graphI z') \<Longrightarrow>
           (inj_on(\<lambda> x. efids_cur(InfrastructureOne.cgra (InfrastructureOne.graphI z) x)) 
                     (actors_graph (InfrastructureOne.graphI z))) \<Longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). 
      efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) \<noteq>
              efids_cur(efids_inc_ind (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))) \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<Longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureOne.cgra (graphI z) a)) \<in> egra (graphI z) l)) \<Longrightarrow>
         (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  a \<in>  agra (graphI z') l' \<longrightarrow>
          efids_cur ((InfrastructureOne.cgra (graphI z') a)) \<in> egra (graphI z') l'))"
  using isthere_lem0 by presburger


lemma isthere_lem00: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  nodes (graphI z) = nodes (graphI z') \<longrightarrow>
           (inj_on(\<lambda> x. efids_cur(InfrastructureOne.cgra (InfrastructureOne.graphI z) x)) 
                     (actors_graph (InfrastructureOne.graphI z))) \<longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). 
      inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))) \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureOne.cgra (graphI z) a)) \<in> egra (graphI z) l)) 
        \<longrightarrow> (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  a \<in>  agra (graphI z') l' \<longrightarrow>
          efids_cur ((InfrastructureOne.cgra (graphI z') a)) \<in> egra (graphI z') l'))"
  apply (rule allI)+
  apply (rule impI)
  apply (rule InfrastructureOne.state_transition_in.cases, assumption)
    apply (simp add: move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
     apply (rule allI)
      apply (rule impI)+
      apply (erule conjE)+
  apply (metis (no_types, lifting) InfrastructureOne.actors_graph_def inj_on_contraD mem_Collect_eq)
  apply (rule impI)+
    apply fastforce
(* get *)
      apply (rule impI)+
  using InfrastructureOne.agra.simps InfrastructureOne.cgra.simps InfrastructureOne.egra.simps InfrastructureOne.graphI.simps apply presburger
(* put *)
  apply (rule impI)+
  apply (rule allI)+
  apply (rule impI)+
  apply simp
  apply (simp add: put_graph_efid_def)
  apply (rule conjI)
  prefer 2
  apply (metis (mono_tags, lifting) InfrastructureOne.actors_graph_def InfrastructureOne.atI_def inj_on_def mem_Collect_eq)
  apply (rule impI)+
  apply (subgoal_tac "l' = l")
   apply simp
  apply (rule_tac z = z and z' = z' and a = a in actor_unique_loc_lem0a)
       prefer 5
  apply simp
  apply force
  apply (meson InfrastructureOne.same_nodes0)
  apply presburger
  apply (metis InfrastructureOne.same_nodes0)
by (simp add: atI_def)

lemma isthere_lem00a: "z \<rightarrow>\<^sub>n z' \<Longrightarrow> nodes (graphI z) = nodes (graphI z') \<Longrightarrow>
           (inj_on(\<lambda> x. efids_cur(InfrastructureOne.cgra (InfrastructureOne.graphI z) x)) 
                     (actors_graph (InfrastructureOne.graphI z))) \<Longrightarrow>
 (\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). 
      inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))) \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>
                a \<in>  agra (graphI z) l \<longrightarrow>  a \<in>  agra (graphI z) l' \<longrightarrow> l = l')) \<Longrightarrow>
         (\<forall> a.
             (\<forall> l. l \<in> nodes (graphI z) \<longrightarrow>  a \<in>  agra (graphI z) l \<longrightarrow>
            efids_cur ((InfrastructureOne.cgra (graphI z) a)) \<in> egra (graphI z) l)) \<Longrightarrow>
         (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI z') \<longrightarrow>  a \<in>  agra (graphI z') l' \<longrightarrow>
          efids_cur ((InfrastructureOne.cgra (graphI z') a)) \<in> egra (graphI z') l'))"
  using isthere_lem00 by presburger





lemma is_there_lem[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
     (\<forall> a \<in> actors_graph (InfrastructureOne.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI I). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter> 
      (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')))) = {}))) \<Longrightarrow>
        (inj_on(\<lambda> x. efids_cur(InfrastructureOne.cgra (InfrastructureOne.graphI I) x)) 
                     (actors_graph (InfrastructureOne.graphI I))) \<Longrightarrow>
        (\<forall> a \<in> actors_graph (InfrastructureOne.graphI I). 
               inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))) \<Longrightarrow>
           (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>
                a \<in>  agra (graphI I) l \<longrightarrow>  a \<in>  agra (graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> a.
             (\<forall> l. l \<in> nodes (graphI I) \<longrightarrow>  a \<in>  agra (graphI I) l \<longrightarrow>
            efids_cur ((InfrastructureOne.cgra (graphI I) a)) \<in> egra (graphI I) l)) \<longrightarrow>
        (\<forall> a. 
           (\<forall> l'. l' \<in> nodes (graphI y) \<longrightarrow>  a \<in>  agra (graphI y) l' \<longrightarrow>
                  efids_cur ((InfrastructureOne.cgra (graphI y) a)) \<in> egra (graphI y) l'))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
              \<forall>a'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')) =
                 {} \<Longrightarrow>
           inj_on (\<lambda>x. efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) x))
            (InfrastructureOne.actors_graph (InfrastructureOne.graphI I)) \<Longrightarrow>
           \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
              inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           (\<forall>a l. l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<longrightarrow>
                  a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>
                  efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)
                  \<in> InfrastructureOne.egra (InfrastructureOne.graphI I) l) \<longrightarrow>
           (\<forall>a l'.
               l' \<in> InfrastructureOne.nodes (InfrastructureOne.graphI y) \<longrightarrow>
               a \<in> InfrastructureOne.agra (InfrastructureOne.graphI y) l' \<longrightarrow>
               efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI y) a)
               \<in> InfrastructureOne.egra (InfrastructureOne.graphI y) l') \<Longrightarrow>
           (\<forall>a l. l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<longrightarrow>
                  a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>
                  efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)
                  \<in> InfrastructureOne.egra (InfrastructureOne.graphI I) l) \<longrightarrow>
           (\<forall>a l'.
               l' \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z) \<longrightarrow>
               a \<in> InfrastructureOne.agra (InfrastructureOne.graphI z) l' \<longrightarrow>
               efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)
               \<in> InfrastructureOne.egra (InfrastructureOne.graphI z) l') "
    apply (rule impI)
  apply (rule_tac z = y in isthere_lem00a)
    apply force
    apply (meson InfrastructureOne.same_nodes r_into_rtrancl)
    using efids_cur_inj_on_inv apply presburger
    apply (metis InfrastructureOne.same_actors efids_list_inj_refl)
    using actor_unique_loc_lem apply presburger
    by meson
qed


lemma ext_image: "\<forall> x \<in> A. f x = g x \<Longrightarrow> f ` A = g ` A"
  by simp

lemma ext_ifte[rule_format]: "(\<forall> a l. P a l = Q a l) \<Longrightarrow> (\<forall> a l. Q a l \<longrightarrow> t a l = r a l) \<Longrightarrow> 
           (\<lambda> x y. if P x y then t x y else t') = (\<lambda> x y. if Q x y then r x y else t')"
  by meson

lemma ext_ifte'[rule_format]: "(\<forall> a l. P a l = Q a l) \<Longrightarrow> (\<forall> a l. Q a l \<longrightarrow> t a l = r a l) \<Longrightarrow> 
           (\<lambda> x. if P x y then t x y else t') = (\<lambda> x. if Q x y then r x y else t')"
  by meson

lemma ext_ifte''[rule_format]: "(\<forall> l. P l = Q l) \<Longrightarrow> (\<forall> l. Q l \<longrightarrow> t l = r l) \<Longrightarrow> 
           (\<lambda> x. if P x then t x else t') = (\<lambda> x. if Q x then r x else t')"
  by meson


(* *)
thm actor_unique_loc_lem

lemma actors_loc_unique: 
"z \<rightarrow>\<^sub>n z' \<Longrightarrow>  (\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l' \<longrightarrow> l = l')) \<Longrightarrow>
 l \<in> nodes (graphI z') \<Longrightarrow> l \<noteq> la \<Longrightarrow>
aa \<in> InfrastructureOne.agra (InfrastructureOne.graphI z') l \<Longrightarrow>
a \<in> InfrastructureOne.agra (InfrastructureOne.graphI z') la \<Longrightarrow> aa \<noteq> a"
  apply (erule contrapos_nn)
  apply (rule actor_unique_loc_lem0a, assumption)
  using InfrastructureOne.same_nodes0 apply presburger
  apply assumption
    apply assumption
   apply assumption
  by (erule ssubst)


(* attempt with agra instead of actors_graph (more specific) *)
lemma efids_cur_eq_egra[rule_format]: "(\<forall> z. (\<forall> z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureOne.graphI z).
\<forall> e \<in> (InfrastructureOne.egra (InfrastructureOne.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureOne.graphI z) l. 
     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureOne.graphI z').
\<forall> e \<in> (InfrastructureOne.egra (InfrastructureOne.graphI z') l).
 (\<exists> a \<in> agra (InfrastructureOne.graphI z') l. 
     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)))))"
proof (clarify, frule same_actors0, frule same_nodes0, rule state_transition_in.cases, assumption)
  show "\<And>z z' l e G I a la l' I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
             \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI z) l.
                e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI z') l \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureOne.nodes G \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes G \<Longrightarrow>
       a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
       InfrastructureOne.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a a la l' (InfrastructureOne.graphI I)) (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI z') l.
          e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)"
    apply (simp add: move_graph_a_def)
    by fastforce
next show "\<And>z z' l e G I a la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
             \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI z) l.
                e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI z') l \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureOne.nodes G \<Longrightarrow>
       InfrastructureOne.enables I la (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)
           (a := (InfrastructureOne.kgra G a)
              (la := {(x, y). x \<in> InfrastructureOne.agra G la \<and> y \<in> InfrastructureOne.egra G la}))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI z') l.
          e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)"
    by simp
next show "\<And>z z' l e G I a la I'.
       z \<rightarrow>\<^sub>n z' \<Longrightarrow>
       \<forall>a l l'.
          l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z) \<longrightarrow>
          a \<in> InfrastructureOne.agra (InfrastructureOne.graphI z) l \<longrightarrow>
          a \<in> InfrastructureOne.agra (InfrastructureOne.graphI z) l' \<longrightarrow> l = l' \<Longrightarrow>
       \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
          \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
             \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI z) l.
                e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI z') l \<Longrightarrow>
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z) =
       InfrastructureOne.actors_graph (InfrastructureOne.graphI z') \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI z) = InfrastructureOne.nodes (InfrastructureOne.graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> la \<Longrightarrow>
       InfrastructureOne.enables I la (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid a la G)
        (InfrastructureOne.delta I) \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI z') l.
          e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)"
    apply (unfold put_graph_efid_def)
    apply (case_tac "l = la")
    apply (smt (z3) DiffE InfrastructureOne.agra.simps InfrastructureOne.atI_def InfrastructureOne.cgra.simps InfrastructureOne.egra.simps InfrastructureOne.graphI.simps fun_upd_apply insertCI insertE)
    apply (drule_tac x = l in bspec)
     apply metis
    apply (subgoal_tac "e \<in> InfrastructureOne.egra (InfrastructureOne.graphI z) l ")
    prefer 2
    apply fastforce
    apply (drule_tac x = e in bspec, assumption)
    apply (erule bexE)
    apply (rule_tac x = aa in bexI)
     apply (simp add: atI_def)
     apply (subgoal_tac "aa \<noteq> a")
      apply simp
    prefer 2
    using InfrastructureOne.agra.simps InfrastructureOne.graphI.simps apply presburger
    by meson
qed

lemma efids_cur_eq_egra_refl[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureOne.graphI I).
\<forall> e \<in> (InfrastructureOne.egra (InfrastructureOne.graphI I) l).
 (\<exists> a \<in> agra (InfrastructureOne.graphI I) l. 
     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureOne.graphI y).
\<forall> e \<in> (InfrastructureOne.egra (InfrastructureOne.graphI y) l).
 (\<exists> a \<in> agra (InfrastructureOne.graphI y) l. 
     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI y) a)))"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. \<forall>a l l'.
              l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           (\<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
               \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
                  \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI I) l.
                     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<longrightarrow>
           (\<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI y).
               \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI y) l.
                  \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI y) l.
                     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI y) a)) \<Longrightarrow>
           (\<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
               \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
                  \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI I) l.
                     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<longrightarrow>
           (\<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
               \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
                  \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI z) l.
                     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))"
    by (simp add: Pair_inject actor_unique_loc_lem case_prodE efids_cur_eq_egra)
qed


lemma efids_cur_efids_list_actor_unique: 
"(\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI z). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<inter> 
      (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a')))) = {}))) \<Longrightarrow>
 a \<in> actors_graph (InfrastructureOne.graphI z) \<Longrightarrow> a' \<in> actors_graph (InfrastructureOne.graphI z) \<Longrightarrow>
efids_cur (cgra (graphI z) a) \<in> range(efids_list (cgra (graphI z) a')) \<Longrightarrow> a = a'"
  by (smt (verit, ccfv_threshold) IntI UNIV_I efidlist.exhaust efids_cur.simps efids_list.simps empty_iff imageE image_eqI)

lemma anonymous_actor_in_agra[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>
InfrastructureOne.actors_graph (InfrastructureOne.graphI z) \<noteq> {} \<longrightarrow>
(\<forall> a \<in> actors_graph (graphI z). inj (efids_list (InfrastructureOne.cgra (graphI z) a))) \<longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI z). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI z). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a)) \<inter> 
      (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI z) a')))) = {}))) \<longrightarrow>
(\<forall> l \<in> nodes (graphI z).
         (\<forall> e \<in> (egra (InfrastructureOne.graphI z) l).
         (\<exists> a \<in> actors_graph (InfrastructureOne.graphI z) . e \<in> range (efids_list (InfrastructureOne.cgra (graphI z) a))))) \<longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI z) \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI z) l' \<longrightarrow> l = l')) \<longrightarrow>
(\<forall> l \<in> nodes(InfrastructureOne.graphI z).
\<forall> e \<in> (InfrastructureOne.egra (InfrastructureOne.graphI z) l).
 (\<exists> a \<in> agra (InfrastructureOne.graphI z) l. 
     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z) a))) \<longrightarrow>
(\<forall> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z).
  \<forall> y \<in> InfrastructureOne.egra (InfrastructureOne.graphI z) l.
  anonymous_actor z y \<in> InfrastructureOne.agra (InfrastructureOne.graphI z) l)  \<longrightarrow>
(\<forall> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI z').
  \<forall> y \<in> InfrastructureOne.egra (InfrastructureOne.graphI z') l.
  anonymous_actor z' y \<in> InfrastructureOne.agra (InfrastructureOne.graphI z') l)"
  apply (rule allI)+
  apply (rule impI)+
  apply (rule ballI)+
  apply (subgoal_tac "(\<forall> l \<in> nodes(InfrastructureOne.graphI z').
\<forall> e \<in> (InfrastructureOne.egra (InfrastructureOne.graphI z') l).
 (\<exists> a \<in> agra (InfrastructureOne.graphI z') l. 
     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI z') a)))")
   prefer 2
   apply (simp add: efids_cur_eq_egra)
  apply (subgoal_tac "\<exists> a' \<in> agra(graphI z') l. y = efids_cur(cgra (graphI z') a')")
  prefer 2
   apply fastforce
  apply (erule bexE)
  apply (subgoal_tac "(\<forall> l \<in> nodes (graphI z').
         (\<forall> e \<in> (egra (InfrastructureOne.graphI z') l).
         (\<exists> a \<in> actors_graph (InfrastructureOne.graphI z') .
          e \<in> range (efids_list (InfrastructureOne.cgra (graphI z') a)))))")
  prefer 2
  using efid_in_range_invariantO apply presburger
  apply (subgoal_tac "(\<exists> a \<in> actors_graph (InfrastructureOne.graphI z') .
          efids_cur(cgra (graphI z') a') \<in> range (efids_list (InfrastructureOne.cgra (graphI z') a)))")
  prefer 2
   apply fastforce
  apply (erule bexE)
  apply (subgoal_tac "a = a'")
  prefer 2
  apply (smt (verit, ccfv_SIG) InfrastructureOne.actors_graph_def InfrastructureOne.same_actors0 efids_cur_efids_list_actor_unique efids_list_eq mem_Collect_eq)
  apply (subgoal_tac "a \<in> InfrastructureOne.agra (InfrastructureOne.graphI z') l ")
   prefer 2
  apply simp
apply (subgoal_tac "\<forall> a'. a' \<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI z')
    \<and> y \<in> range (efids_list (InfrastructureOne.cgra (graphI z') a'))
   \<longrightarrow> a' = anonymous_actor z' y")
  prefer 2
   apply (simp add: InfrastructureOne.same_actors0 anonymous_actor_def1b efids_list_eq)
  apply (subgoal_tac "a = anonymous_actor z' y ")
  prefer 2
   apply presburger
  apply (rotate_tac -1)
  apply (erule subst)
  by assumption


lemma anonymous_actor_invOO[rule_format]: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<noteq> {} \<Longrightarrow>
(\<forall> a \<in> actors_graph (graphI I). inj (efids_list (InfrastructureOne.cgra (graphI I) a))) \<Longrightarrow>
(\<forall> a \<in> actors_graph (InfrastructureOne.graphI I). (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI I). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter> 
      (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')))) = {}))) \<Longrightarrow>
(\<forall> l \<in> nodes (graphI I).
         (\<forall> e \<in> (egra (InfrastructureOne.graphI I) l).
         (\<exists> a \<in> actors_graph (graphI I). e \<in> range (efids_list (InfrastructureOne.cgra (graphI I) a))))) \<Longrightarrow>
(\<forall> a.
             (\<forall> l l'. l \<in> nodes (graphI I) \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>  
                a \<in>  InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> l = l')) \<Longrightarrow>
(\<forall> l \<in> nodes(InfrastructureOne.graphI I).
\<forall> e \<in> (InfrastructureOne.egra (InfrastructureOne.graphI I) l).
 (\<exists> a \<in> agra(InfrastructureOne.graphI I) l. 
     e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))) \<Longrightarrow>
(\<forall> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I).
  \<forall> e \<in> InfrastructureOne.egra (InfrastructureOne.graphI I) l.
  anonymous_actor I e \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l)  \<longrightarrow>
(\<forall> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI y).
  \<forall> e \<in> InfrastructureOne.egra (InfrastructureOne.graphI y) l.
  anonymous_actor y e \<in> InfrastructureOne.agra (InfrastructureOne.graphI y) l)"
proof (erule rtrancl_induct, simp)
  show "\<And>y z. InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<noteq> {} \<Longrightarrow>
           \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
              inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
           \<forall>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
              \<forall>a'\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                 a \<noteq> a' \<longrightarrow>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<inter>
                 range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a')) =
                 {} \<Longrightarrow>
           \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
              \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
                 \<exists>a\<in>InfrastructureOne.actors_graph (InfrastructureOne.graphI I).
                    e \<in> range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) \<Longrightarrow>
           \<forall>a l l'.
              l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I) \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l \<longrightarrow>
              a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
           \<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
              \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
                 \<exists>a\<in> agra (InfrastructureOne.graphI I) l.
                    e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a) \<Longrightarrow>
           (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           (\<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
               \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
                  anonymous_actor I e \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l) \<longrightarrow>
           (\<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI y).
               \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI y) l.
                  anonymous_actor y e \<in> InfrastructureOne.agra (InfrastructureOne.graphI y) l) \<Longrightarrow>
           (\<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI I).
               \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI I) l.
                  anonymous_actor I e \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l) \<longrightarrow>
           (\<forall>l\<in>InfrastructureOne.nodes (InfrastructureOne.graphI z).
               \<forall>e\<in>InfrastructureOne.egra (InfrastructureOne.graphI z) l.
                  anonymous_actor z e \<in> InfrastructureOne.agra (InfrastructureOne.graphI z) l)"
    apply (rule impI)
    apply (rule ballI)+
    thm anonymous_actor_in_agra
    apply (rule_tac z' = z in anonymous_actor_in_agra)
    apply simp
    using InfrastructureOne.same_actors apply force
    apply (metis InfrastructureOne.same_actors efids_list_inj_refl)
    apply (metis ran_efids_list_disjoint_refl)
    apply (metis efids_in_range_invariantOO)
    using actor_unique_loc_lem apply presburger
    apply (simp add: efids_cur_eq_egra_refl)
    apply fastforce
by assumption+
qed

end

 