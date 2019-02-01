theory ringBufFifo imports paraGste1
begin
abbreviation rst::"expType" where
"rst \<equiv> IVar (Ident ''rst'')"

abbreviation push::"expType" where
"push \<equiv> IVar (Ident ''push'')"

abbreviation pop::"expType" where
"pop \<equiv> IVar (Ident ''pop'')"

abbreviation dataIn::"expType" where
"dataIn \<equiv> IVar (Ident ''dataIn'' )"



abbreviation LOW::"expType" where
"LOW \<equiv> Const (boolV False)"
abbreviation HIGH::"expType" where
" HIGH \<equiv> Const (boolV True)"

abbreviation emptyFifo::"expType" where
" emptyFifo \<equiv> IVar (Ident ''empty'' ) "

abbreviation tail::"expType" where
" tail \<equiv> IVar (Ident ''tail'' ) "

abbreviation head::"expType" where
" head \<equiv> IVar (Ident ''head'' ) "


abbreviation full::"expType" where
" full \<equiv> IVar (Ident ''full'' ) "

definition fullForm::"formula" where [simp]:
" fullForm \<equiv> eqn full HIGH "

abbreviation mem::"varType" where
"mem \<equiv>  ( (Ident ''mem'') )"

type_synonym paraExpType="nat \<Rightarrow>expType"

 

abbreviation dataOut::"nat\<Rightarrow>expType" where
"dataOut DEPTH \<equiv> read (Ident ''mem'') DEPTH (IVar (Ident ''head'' ))"


abbreviation rstForm::"formula" where
"rstForm  \<equiv>  (eqn rst HIGH)"

abbreviation emptyForm::"formula" where
"emptyForm  \<equiv>  (eqn emptyFifo HIGH)"
 
abbreviation pushForm::"formula" where
"pushForm \<equiv> andForm (andForm (eqn rst LOW) (eqn push HIGH)) (eqn pop LOW)"

abbreviation popForm::"formula" where
"popForm \<equiv> andForm (andForm (eqn rst LOW) (eqn push LOW)) (eqn pop HIGH)"

abbreviation nPushPopForm::"formula" where
"nPushPopForm \<equiv> andForm (andForm (eqn rst LOW) (eqn push LOW)) (eqn pop LOW)"

abbreviation pushDataForm::"nat \<Rightarrow>formula" where
" pushDataForm D \<equiv>andForm pushForm  (eqn dataIn (Const (index D)))"

abbreviation popDataForm::"nat\<Rightarrow>nat \<Rightarrow>formula" where
" popDataForm DEPTH D \<equiv>  (eqn (dataOut DEPTH) (Const (index D)))"
 
abbreviation nFullForm::"formula" where
"nFullForm \<equiv>  neg (fullForm )"

abbreviation nEmptyForm::"formula" where
"nEmptyForm \<equiv> neg emptyForm "



definition  vertexI::"node" where [simp]:
"vertexI \<equiv>Vertex  0"

(*DEPTH=LAST + 1*)
definition  vertexL::"nat \<Rightarrow> node list" where [simp]:
"vertexL LAST  \<equiv>  vertexI # (map (%i. Vertex  i) (down LAST))"

definition edgeL::"nat \<Rightarrow> edge list" where [simp]:
 "edgeL LAST \<equiv> [Edge vertexI ( Vertex 1)]
    @ [Edge  ( Vertex 1) ( Vertex 3)]		
    @ [Edge  ( Vertex 1) ( Vertex 4)]	
    
		@(map (%i.  ( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) ) (upt 0  (LAST+2) ))  (* self-loop*)  
	  @(map (%i.  ( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) (upt 1 (LAST+2) ))  (* self-loop*)   
	  
		@(map (%i.   ( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 3))) ) ( upt 1 (LAST+1)))
		@(map (%i.   ( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 4))) ) ( upt 1 (LAST+1)))
		
		@(map (%i.   ( Edge (Vertex (2 * i + 3))  (Vertex (2 * i + 1))) ) (  upt 0 (LAST+1) )) 
		@(map (%i.   ( Edge (Vertex (2 * i + 4))  (Vertex (2 * i +2 ))) ) (  upt 1 (LAST+1) ))
		@[ Edge (Vertex 4) (Vertex 1)]
	 "


(*
edgeL LAST \<equiv> [Edge vertexI ( Vertex 1)]
    @ [Edge  ( Vertex 1) ( Vertex 3)]		
    @ [Edge  ( Vertex 1) ( Vertex 4)]	
    
		@(map (%i.  ( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) ) (upt 0  (LAST+2) ))  (* self-loop*)  
	  @(map (%i.  ( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) (upt 1  (LAST+2) ))  (* self-loop*)   
	  
		@(map (%i.   ( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 3))) ) ( upt 1 (LAST+1)))
		@(map (%i.   ( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 4))) ) ( upt 1 (LAST+1)))
		
		@(map (%i.   ( Edge (Vertex (2 * i + 3))  (Vertex (2 * i + 1))) ) (  upt 0 (LAST+1) )) 
		@(map (%i.   ( Edge (Vertex (2 * i + 4))  (Vertex (2 * i + 2))) ) (  upt 1 (LAST+1) ))
		@[Edge  ( Vertex 4) ( Vertex 1)]
;*)
primrec node2Nat::"node \<Rightarrow> nat" where
"node2Nat (Vertex n) = n"


definition antOfRbFifo::"nat\<Rightarrow>edge\<Rightarrow>formula" where [simp]:
"antOfRbFifo  D  edge\<equiv>
  (let from=node2Nat (source edge) in
   let to=node2Nat (sink edge) in
  ( if (	from = 0) then rstForm	else
     if (from=to) then nPushPopForm else
   ( if ((from mod 2) =1) then
     (
       if ((from + 2)=to) then ( pushForm ) else
       if (from=(to + 2)) then popForm else
       pushDataForm D )   else 
     popForm)))"


(*definition antOfRbFifo::"nat\<Rightarrow>edge\<Rightarrow>formula" where [simp]:
"antOfRbFifo  D  edge\<equiv>
  (let from=node2Nat (source edge) in
   let to=node2Nat (sink edge) in
   if (from = 0) then rstForm	else
   if (from=to) then nPushPopForm else
      (if ((from mod 2) =1) then
        (
          if ((from + 2)=to) then ( pushForm ) else
          if (from=(to + 2)) then popForm else
          pushDataForm D )   
       else popForm))"



definition consOfRbFifo::"nat\<Rightarrow>nat\<Rightarrow>edge \<Rightarrow>formula" where  [simp]:
"consOfRbFifo   D LAST edge \<equiv>
(let from=node2Nat (source edge) in
 let to=node2Nat (sink edge) in
 if 	(((from mod 2) = 1) \<and> ((to mod 2) = 1)) then
    (if  from =1 then (andForm  emptyForm (nFullForm LAST))
     else if    (from = (2*LAST+3)) then (andForm nEmptyForm (fullForm LAST)) 
     else andForm nEmptyForm (nFullForm LAST))
 else if (from=4 \<and> to = 1) then popDataForm LAST D
 else if (from = (2*LAST+4)) then (andForm nEmptyForm (fullForm LAST)) 
 else if (from =1 )  then (andForm emptyForm (nFullForm LAST))
 else if (from \<noteq>0)   then (andForm nEmptyForm (nFullForm LAST))
 else chaos)"

let cons aEdge = 
	val (Edge (Vertex from) (Vertex to)) = aEdge
in
	((from%2) = 1) AND ((to%2) = 1) => 				
		(from = 1) => TAndList [empty,nFull]		//FIFO is empty
	|	(from = (2*DEPTH+1)) => TAndList [nEmpty,full]	//FIFO is full
	|	TAndList [nEmpty,nFull]					//FIFO of other size
|	(to = 2) => popData vOfDataIn					//read the write data
| 	TAndList []
;*)

definition consOfRbFifo::"nat\<Rightarrow>nat\<Rightarrow>edge \<Rightarrow>formula" where  [simp]:
"consOfRbFifo   D LAST edge \<equiv>
let from=node2Nat (source edge) in
let to=node2Nat (sink edge) in
 (if 	(((from mod 2) = 1) \<and> ((to mod 2) = 1)) then
  (if  from =1 then (andForm  emptyForm (nFullForm))
  else if    (from = (2*LAST+3)) then (andForm nEmptyForm (fullForm )) 
  else andForm nEmptyForm (nFullForm ))
 else if (from=4 \<and> to = 1) then popDataForm LAST D
 else if (from = (2*LAST+4)) then (andForm nEmptyForm (fullForm)) 
 else if (from =1 )  then (andForm emptyForm (nFullForm ))
 else if (from \<noteq>0)   then (andForm nEmptyForm (nFullForm))
 else chaos)"

definition rbFifoGsteSpec::" nat\<Rightarrow>nat\<Rightarrow>gsteSpec" where  [simp]:
"rbFifoGsteSpec LAST  data\<equiv>
  Graph  vertexI (edgeL  LAST ) (antOfRbFifo data )  (consOfRbFifo data  LAST)"

primrec applyPlusN::"expType\<Rightarrow>nat \<Rightarrow>expType" where
"applyPlusN e 0=e" |
"applyPlusN e (Suc N) = uif ''+'' [applyPlusN e N, Const (index 1)]"

definition tagFunOfRingBufFifo:: " nat\<Rightarrow>nat\<Rightarrow>nodeTagFuncList" where [simp]:
"tagFunOfRingBufFifo DATA LAST  n \<equiv> 
  let x=node2Nat n in
   let DataE=(Const (index DATA)) in
   let LASTE=(Const (index LAST)) in
   let TwiceLASTPlus3=(Const (index (2*LAST +3))) in
   let tailPlus=uif ''+'' [tail, (Const (index 1))] in
   let headPlus=uif ''+'' [head, (Const (index 1))] in
   if (x = 0) then [] else
    (if ((x mod 2) = 1) then 
      (if (x =1) then 
        [eqn tail head, eqn  emptyFifo HIGH,
        eqn full LOW,uip ''le'' [head,LASTE]]
       else 
       (if (x=2*LAST+3) then 
        [eqn tail (applyPlusN head (x div 2  )), 
        eqn  emptyFifo LOW,
        (*eqn emptyFifo (iteForm (eqn tail  headPlus)  HIGH emptyFifo),
        eqn full (iteForm (eqn tailPlus  head)  HIGH full),*)
        eqn full  HIGH,
        uip ''le'' [head,LASTE]
        ] 
        else 
         [eqn tail (applyPlusN head (x div 2  )), 
         eqn  emptyFifo LOW,
         eqn full LOW,uip ''le'' [head,LASTE]]
         (* eqn emptyFifo (iteForm (eqn tail  headPlus)  HIGH emptyFifo),
          eqn full (iteForm (eqn tailPlus  head)  HIGH full),*)
        (* uip ''le'' [head,LASTE]]*) ) )
    else 
    ((*if (x = 2) then [] 
     else *)
        (if (x=2*LAST+4) then 
        [eqn tail (applyPlusN head (x div 2 - 1 ) ), 
        eqn emptyFifo LOW, 
        eqn full HIGH,uip ''le'' [head,LASTE],
        eqn (read mem LAST (applyPlusN head (x div 2  - 2))) DataE ] 
        else 
         [eqn tail (applyPlusN head (x div 2  - 1)), eqn  emptyFifo LOW,
         eqn full LOW, uip ''le'' [head,LASTE],
         
          eqn (read mem LAST (applyPlusN head (x div 2  - 2))) DataE ]))
     )
   
 "
 
 abbreviation branch1::"generalizeStatement" where 
"branch1 \<equiv> 
  (let S1=assign (Ident ''head'',(Const (index 0))) in
   let S2=assign (Ident ''tail'',(Const (index 0))) in
   let S3=assign (Ident ''empty'',HIGH) in
   let S4=assign (Ident ''full'',LOW) in 
   Parallel [S1,S2,S3,S4])"
   
abbreviation branch2::"nat\<Rightarrow>generalizeStatement" where 
"branch2 LAST \<equiv> 
  (let S1=map (\<lambda>i. assign ((Para (Ident ''mem'') i), 
    iteForm (eqn tail (Const (index i)))  dataIn 
    (IVar (Para (Ident ''mem'')  i)))) (down LAST ) in
   let tailPlus=uif ''+'' [tail, (Const (index 1))] in
   let S2=assign (Ident ''tail'', tailPlus ) in
   let S3=assign (Ident ''empty'',LOW) in
   let S4=assign (Ident ''full'',iteForm (eqn tailPlus  head)  HIGH full) in
   (* Parallel (S1@[S2,S3]))*)
   Parallel ([S2,S3,S4]@S1))"   
   
abbreviation branch3::"generalizeStatement" where 
"branch3 \<equiv> 
  (let headPlus=uif ''+'' [head, (Const (index 1))] in
    Parallel [
    assign (Ident ''empty'',iteForm (eqn tail  headPlus)  HIGH emptyFifo),
    assign (Ident ''full'', LOW),
    assign (Ident ''head'',  headPlus)] )
    " 

 
abbreviation ringBuffifo::" nat\<Rightarrow>generalizeStatement" where
"ringBuffifo  LAST\<equiv> 
  caseStatement 
     [(eqn rst HIGH, branch1),
      (andForm (eqn push HIGH) (nFullForm), branch2 LAST),
      (andForm (eqn pop HIGH) (eqn emptyFifo LOW), branch3)] 
   "
   

consts J::"nat \<Rightarrow> interpretFunType"  
  
axiomatization where axiomOnIAdd [simp,intro]:
"  J LAST ''+'' [index m,   index (Suc 0)] = index ((m + 1) mod (Suc LAST  ))"
(* (if m=LAST  then (index 0) else (index (m +1 )))"
index ((m + 1) mod (Suc LAST  )) " *)

axiomatization where axiomOnLe [simp,intro]:  
"  J LAST  ''le'' [op1, op2]  = boolV (\<exists> i1. \<exists> i2. (op1=index i1) \<and> (op2=index i2) \<and>  (i1 \<le> i2))" 

(*axiomatization where headIsIndex[simp,intro]:"\<exists>i. ((s (Ident ''head'') ) = (index i)) "

*)

lemma test0: "formEval (J LAST) (eqn (Var tail) (applyPlusN head i) ) s  \<longrightarrow>
formEval (J LAST) (eqn (uif ''+''  [Var tail, Const (index 1)]) (applyPlusN head (i+1)) ) s"
apply(auto) done

lemma auxOnReadWrite[simp]:
"expEval I e s=expEval I e' s \<and>expEval I e s=index i\<and> i\<le> LAST \<longrightarrow>(\<forall>j. Para mem j \<notin>set (varOfExp e'))\<longrightarrow> 

        expEval I  (substExp (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down LAST)))
            (map (\<lambda>i. (Para mem i, iteForm (eqn e (Const (index i))) e'' (IVar (Para mem i))))
              (down LAST)))
          s = expEval I e'' s "   (is "?P LAST")
proof(induct_tac LAST) 
  show "?P 0"
  proof(rule impI)+
  assume a1:" expEval I e s = expEval I e' s \<and> expEval I e s = index i \<and> i \<le> 0" and 
   a2:" \<forall>j. Para mem j \<notin> set (varOfExp e')"
   have a3:"(Para mem 0) \<notin> set (varOfExp e')"
    by(cut_tac a2,auto)
  show " expEval I
     (substExp (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down 0)))
       (map (\<lambda>i. (Para mem i, iteForm (eqn e (Const (index i))) e'' (IVar (Para mem i)))) (down 0)))
     s =
    expEval I e'' s"
   using a1 a3 noEffectSubstExp proof(cut_tac a1,auto)qed
   qed
  next
  fix n
  assume a0:  "?P n"
  show "?P (Suc n)"
  proof(rule impI)+
  assume a1:" expEval I e s = expEval I e' s \<and> expEval I e s = index i \<and> i \<le> Suc n" and 
   a2:" \<forall>j. Para mem j \<notin> set (varOfExp e')"
   have a3:"(Para mem  (Suc n)) \<notin> set (varOfExp e')"
    by(cut_tac a2,auto) 
   show "expEval I
     (substExp (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down (Suc n))))
       (map (\<lambda>i. (Para mem i, iteForm (eqn e (Const (index i))) e'' (IVar (Para mem i)))) (down (Suc n))))
     s =
    expEval I e'' s" (is "?LHS (Suc n) =?RHS")
   proof(case_tac "i \<le> n")
     assume b1:"i \<le> n"
     have b2:" (Para mem (Suc n)) \<notin> set (varOfExp
     (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down n))))" 
      apply(auto)
      apply (simp add: SucnIsNotInDownn)
      by (simp add: a3)
      
     have b3:"?LHS (Suc n) =?LHS n" 
     using a1 a2 a3 b1 b2 by auto
     have b4:"?LHS n =   expEval I e'' s"
     using a1 b1 a2 a0 apply auto  done
     show "?LHS (Suc n) =?RHS"
     using b4 b3 by auto
   next
    assume b1:"\<not>i \<le> n"
    have b2:"i=Suc n" 
    using b1 a1 by auto
    show "?LHS (Suc n) =?RHS"
     using b1 b2 a1 a2 a3  apply auto done
  qed
qed  
qed

lemma caseExpCong:
  assumes a:"tautlogy (eqn e e') I"
  shows "expEval I   (caseExp (map (\<lambda>i. (eqn e (Const (index i)), IVar (Para mem i))) (down LAST))) s
  =expEval I  (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down LAST))) s"
proof(induct_tac LAST,(cut_tac a,simp)+)qed

lemma caseExpCong1:
  assumes a:"formEval I (eqn e e') s "
  shows "expEval I   (caseExp (map (\<lambda>i. (eqn e (Const (index i)), IVar (Para mem i))) (down LAST))) s
  =expEval I  (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down LAST))) s"
proof(induct_tac LAST,(cut_tac a,simp)+)qed

lemma readWrite[simp,intro!]:
assumes a1:"expEval I e s=expEval I e' s " and a2:"expEval I e s=index i" and a3:" i\<le> LAST " and
a2:"(\<forall>j. Para mem j \<notin>set (varOfExp e'))" 

shows " expEval I  (substExp (caseExp (map (\<lambda>i. (eqn e' (Const (index i)), IVar (Para mem i))) (down LAST)))
            (map (\<lambda>i. (Para mem i, iteForm (eqn e (Const (index i))) e'' (IVar (Para mem i))))
              (down LAST)))
          s = expEval I e'' s "
using a2 a3 assms(2) auxOnReadWrite local.a1 by blast



lemma varOfApplyPlus[simp]:
  "varOfExp (applyPlusN head i) = [(Ident ''head'' )]"
  apply(induct_tac i,auto) done
  
lemma onApplyPlusI[simp]:"i \<le> LAST \<longrightarrow> 
  j \<le> LAST \<longrightarrow> s (Ident ''head'') = index j \<longrightarrow> 
  expEval (J LAST) (applyPlusN head i) s = index ((j + i) mod (Suc LAST))  "
  proof(induct_tac i,auto,arith) qed
  
lemma onApplyPlusII[simp]:"0<i\<longrightarrow>i\<le> LAST \<longrightarrow> 
  j \<le> LAST \<longrightarrow> s (Ident ''head'') = index j \<longrightarrow>  
expEval (J LAST) (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (i - Suc 0)) s = index ((j + i) mod (Suc LAST))" (is "?P i")
  proof(induct_tac i,simp,case_tac "n=0",simp) 
    fix n
    assume a:"?P n" and b:"~n=0"
    show "?P (Suc n)"
    proof(rule impI)+
      assume c1:"0< Suc n" and c2:"Suc n \<le> LAST" and c3:"j \<le> LAST" and c4:"s (Ident ''head'') = index j"
      show "
      expEval (J LAST) (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (Suc n - Suc 0)) s = index ((j + Suc n) mod Suc LAST)"
      (is "?LHS =?RHS")
      proof -
      have d1:"0<n" by(cut_tac b,simp)
      have d2:"n <LAST" by(cut_tac c2,simp)
      have d3:"(applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (Suc n - Suc 0)) = 
      uif ''+'' [(applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (n -Suc 0)), Const (index (Suc 0))]"
      by (metis One_nat_def Suc_pred applyPlusN.simps(2) d1 diff_Suc_1)
      have d4:"expEval (J LAST) (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (n - Suc 0)) s=index ((j + n) mod (Suc LAST))"
        apply(cut_tac a d1 d2 d3 c3 c4,simp) done

      show "?LHS=?RHS"
      apply(cut_tac d3 d4,simp)
      using mod_Suc_eq_Suc_mod by auto
    qed  
   qed
qed


  
 
lemma test1[simp]: " (expEval (J LAST) (applyPlusN head (Suc i)) s) = J LAST ''+'' [expEval (J LAST) (applyPlusN head i) s, index (Suc 0)]"  
  apply simp done

 

lemma test2[simp]:"Suc j \<le> LAST \<longrightarrow> (Suc j + (Suc LAST)) mod (Suc LAST) =Suc ((j + (Suc LAST)) mod (Suc LAST))" (is "?P j")
by (metis Divides.mod_less le_less_trans lessI less_trans mod_add_self2)
  
lemma test3:"j \<le> LAST \<longrightarrow> (j + (Suc LAST)) mod (Suc LAST) =j" (is "?P j")
by (metis Divides.mod_less le_imp_less_Suc mod_add_self2)


lemma test4[simp]:"0<LAST \<longrightarrow>i < Suc LAST \<longrightarrow> 0 < i \<longrightarrow>
  j \<le> LAST \<longrightarrow> ((j + i) mod (Suc LAST)) =
  (if (j+i)< (Suc LAST) then j+i else (j+i -(Suc LAST)))"  (is "?P LAST")
  using le_mod_geq by force  

(*Suc (if i1 + i < Suc LAST then i1 + i else i1 + i - Suc LAST) mod Suc LAST = i1"*)

lemma test5Aux[simp]:"0<LAST \<longrightarrow>i < Suc LAST \<longrightarrow> 0 < i \<longrightarrow>
  j \<le> LAST \<longrightarrow> ((j + i) mod (Suc LAST)) \<noteq> j"
using nat_neq_iff not_less by auto 

lemma test5:
  assumes a1:" 0 < LAST " and a2:" i < Suc LAST" and a3:" 0 < i " and 
  a4:"j \<le> LAST"
  shows " ((j + i) mod (Suc LAST)) \<noteq> j"
      using a1 a2 a3 a4 test5Aux by auto  
  
(*lemma test:"0<LAST\<longrightarrow>Suc (if i1 = 0 then i1 + LAST else i1 + LAST - Suc LAST) mod Suc LAST = i1"*)
  
lemma  iPlus1IsNotI:
  assumes a1:"0 < LAST" and 
  a2:"J LAST ''+'' [s (Ident ''head''), index (Suc 0)] = s (Ident ''head'')" 
  and a3:" scalar2Bool (J LAST ''le'' [s (Ident ''head''), index LAST])"
  shows False 
  proof -
    have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
      apply(cut_tac a1 a3,auto) done
    then obtain i where b1:"((s (Ident ''head'') ) = (index i))"
      by blast
   (* have b2:"i\<le> LAST"
     using a1 a3 b1 axiomOnLe  apply auto        done*)
    show False
       apply(cut_tac a1 a2 b1 ,case_tac "i=LAST",auto)
       by (metis mod_Suc mod_mod_trivial n_not_Suc_n nat.inject)
      
  qed 

lemma iPlusSucLatIsi:  
  assumes a:" scalar2Bool (J LAST ''le'' [s (Ident ''head''), index LAST])"
  shows "J LAST ''+'' [expEval (J LAST) (applyPlusN head LAST) s, index (Suc 0)]=  s (Ident ''head'')"
 
 proof -
    have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
      apply(cut_tac a,auto) done
    then obtain i where b1:"((s (Ident ''head'') ) = (index i))"
      by blast
    have b2:"i\<le> LAST"
     using a b1 axiomOnLe  apply auto   done
    show ?thesis
    apply(cut_tac b1 b2,simp)
    by (metis (full_types) Divides.mod_less add.commute add_Suc le_imp_less_Suc mod_Suc_eq_Suc_mod mod_add_self1)
qed 

lemma substApplyHead[simp]:
  "substExp (applyPlusN head n) [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])] =
         applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) n"
proof(induct_tac n,auto)qed

(*lemma iplus:
  assumes a1:"0 < LAST"  and a2:"i \<le> LAST" and
  a3:"s (Ident ''head'') = index i" a
shows "j \<le>LAST \<longrightarrow> expEval (J LAST) (substExp (applyPlusN head j) [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])]) s
      = index (( i+1) mod (LAST +1))"
proof(cut_tac a1 a2 a3,induct_tac j,auto)
  show "J 0 ''+'' [s (Ident ''head''), index (Suc 0)] = index 0"*)
(*lemma  iPlusjPLUSIsNotj:
  assumes a1:"0 < LAST"  and a4:"i < LAST" and
  a3:" scalar2Bool (J LAST ''le'' [s (Ident ''head''), index LAST])"
          
  shows "J LAST ''+'' [expEval (J LAST) (applyPlusN head i) s, index (Suc 0)]\<noteq>s (Ident ''head'')" 
proof -
    have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
      using headIsIndex by auto
    then obtain j where b1:"((s (Ident ''head'') ) = (index j))"
      by blast
    have b2:"j\<le> LAST"
     using a1 a3 b1 axiomOnLe  apply auto        done
    have b3: "J LAST ''+'' [expEval (J LAST) (applyPlusN head i) s, index (Suc 0)]  =index ((j + Suc i) mod (Suc LAST))"
    by (metis Suc_eq_plus1 a4 b1 b2 discrete le_Suc_eq onApplyPlusI test1)
 
    have b4:"Suc i< Suc LAST"
    by (simp add: a4)  thm test5
    have b5:"((j + (Suc i)) mod (Suc LAST)) \<noteq>j"  
    apply (cut_tac a1  b2 b4 ,rule test5,auto) 
    done
    with b3 show "J LAST ''+'' [expEval (J LAST) (applyPlusN head i) s, index (Suc 0)] \<noteq> s (Ident ''head'')"
    by (simp add: b1)
       
qed
lemma substApplyHead[simp]:
  "substExp (applyPlusN head n) [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])] =
         applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) n"
proof(induct_tac n,auto)qed         

lemma applyIPlusIsPlusI:
"J LAST ''+'' [expEval (J LAST) (applyPlusN head i) s, index (Suc 0)] =
         expEval (J LAST) (substExp (applyPlusN head i) 
         [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])]) s"
proof(induct_tac i,auto)qed

lemma substCaseExp:
  "substExp
   (caseExp
     (map (\<lambda>i. (g i,e i)) (down LAST)))
      subst0 =
    caseExp
      (map (\<lambda>i. (substForm (g i) subst0, substExp (e i) subst0))
      (down LAST))"        (is "?P LAST")
proof(induct_tac LAST,simp)
  fix n
  assume b:"?P n"
  show "?P (Suc n)" (is "substExp (?caseExp (Suc n)) subst0= caseExp (?list (Suc n))")
  proof -
  have c1:"substExp (?caseExp (Suc n)) subst0=
          substExp (caseExp ((g (Suc n), e (Suc n))#(map (\<lambda>i. (g i,e i)) (down n)))) subst0" (is "?LHS =?RHS1")
    apply (simp only:downSuc ,auto) done
  have c2:"?RHS1 =iteForm (substForm (g (Suc n)) subst0) (substExp (e (Suc n)) subst0) (caseExp (?list n))"
      (is "?RHS1=?RHS2")
      by (simp add: b)
  have c3:"?RHS2=caseExp ((substForm (g (Suc n)) subst0,substExp (e (Suc n)) subst0)#(?list n))"
      (is "?RHS2=?RHS3")
    by(simp )
  have c4:"?RHS3=caseExp (?list (Suc n))"
    by simp
    with c1 c2 c3 show "?P (Suc n)" 
    by presburger
  qed
qed


    
lemma substCaseExp1:
  "substExp
   (caseExp
     (map (\<lambda>i. (eqn (applyPlusN head (j - Suc 0)) (Const (index i)), IVar (Para mem i))) (down LAST)))
      [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])] =
    caseExp
      (map (\<lambda>i. (eqn (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (j - Suc 0)) (Const (index i)), IVar (Para mem i)))
      (down LAST))"        (is "?P LAST")
using substCaseExp by auto
*) 
lemma consistencyOfRbfifo0:
  assumes a:"LAST=0 "
  shows "consistent' (ringBuffifo LAST ) (J LAST) (rbFifoGsteSpec LAST  data) 
  (tagFunOfRingBufFifo  data LAST)"
  proof(unfold consistent'_def,rule allI,rule impI)
    fix e
    let ?G=" (rbFifoGsteSpec LAST  data)"
    let ?M="(ringBuffifo LAST )"
    let ?tag="(tagFunOfRingBufFifo  data LAST)"
    let ?P ="\<lambda>e.   
    (let f=andListForm (?tag (sink e)) in
    let f'=andListForm (?tag (source e)) in
    tautlogy (implyForm (andForm f' (antOf ?G e)) (preCond1  f  ( ?M))) (J LAST))"
    
    assume a1:"e \<in> edgesOf (rbFifoGsteSpec LAST  data)"
    
    have "e=Edge vertexI ( Vertex 1) | 
          e=Edge  ( Vertex 1) ( Vertex 3) |
          e=Edge  ( Vertex 1) ( Vertex 4)|
           (\<exists>i. 0\<le>i \<and> i\<le> LAST + 1 \<and>  e=( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) )   |
            (\<exists>i. 1\<le>i \<and> i\<le> LAST + 1 \<and>  e=( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) |
            
           e=Edge  ( Vertex 3) ( Vertex 1) |
           e=Edge (Vertex 4) (Vertex 1)"
      apply(cut_tac a a1,auto)  done
   moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac b1, simp add:antOfRbFifo_def Let_def)
     done
     }
    moreover
    {assume b1:" (\<exists>i. 0\<le>i \<and> i\<le> LAST +1  \<and>  e=( Edge (Vertex (2* i + 1))  (Vertex (  2*i + 1))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac b2, simp add:antOfRbFifo_def substNIl) done
    }
    moreover
    {assume b1:" (\<exists>i. 1\<le>i \<and> i\<le> LAST+1 \<and>  e=( Edge (Vertex (2* i + 2))  (Vertex (  2*i + 2))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac b2, simp add:antOfRbFifo_def substNIl) done
    }  
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 3) "
        
      (* let ?P' ="\<lambda>e.   
       (let f=andListForm (?tag (sink e)) in
       let f'=andListForm (?tag (source e)) in
       tautlogy (implyForm (andForm f' (antOf ?G e)) (preCond1  f  (branch2 LAST))) (J LAST))"
       
        let ?P1="\<lambda>e.   
       (let f=andListForm (?tag (sink e)) in
       let f'=andListForm (?tag (source e)) in
       let tailPlus=uif ''+'' [tail, (Const (index 1))] in
       let f1=andListForm [eqn tailPlus (applyPlusN head 1), eqn  LOW LOW,
         eqn full LOW, uip ''le'' [head,LASTE]] in
       tautlogy (implyForm (andForm f' (antOf ?G e)) f1) (J LAST))" 
       have c1:"?P e= ?P' e"
        by (simp add: a b1 del:tautlogy_def,auto)*)
       
      
      (* have c2:"?P' e=?P1 e"  
        apply (cut_tac a b1,simp del:tautlogy_def add:Let_def) 
        apply(rule onIfExpPos)
        apply*)
       have "?P e "
       proof(cut_tac a b1,auto simp add:Let_def )  
      (* fix s
       assume c1:"scalar2Bool (J 0 ''le'' [s (Ident ''head''), index 0]) " and
       c2:" J 0 ''+'' [s (Ident ''head''), index (Suc 0)] \<noteq> s (Ident ''head'')"
       have "(s (Ident ''head'') ) = (index 0)"
         apply(cut_tac c1,simp)
       have "\<exists>i. ((s (Ident ''head'') ) = (index i))" 
       using c1 by auto
       then obtain i where b1:"((s (Ident ''head'') ) = (index i))"
          by blast
       have b2:"i=0" 
       using a c1 b1 axiomOnLe  apply auto        done
       show False
       apply(cut_tac b1 b2 c2 , auto) done*)
       
       qed
          
    }
    
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 4) "
      let ?f="andForm (neg (eqn rst HIGH)) (andForm (eqn push HIGH) nFullForm ) " 
       have "?P e "
       proof(cut_tac a b1,auto simp add:Let_def)
        (*  fix s::state
          assume c1:"s (Ident ''head'') \<noteq> index 0 " and
          c2:"scalar2Bool (J 0 ''le'' [s (Ident ''head''), index 0])"
          have "\<exists>i. ((s (Ident ''head'') ) = (index i))" 
             using headIsIndex by auto
          then obtain i where b1:"((s (Ident ''head'') ) = (index i))"
             by blast
          have b2:"i=0" 
            using a c2 b1 axiomOnLe  apply auto        done
          show False
          apply(cut_tac b1 b2 c1 , auto) done*)
       qed
    }
    moreover
    {assume b1:"e=Edge  ( Vertex 3) ( Vertex 1)"
     
     have b3:"varOfExp (applyPlusN head i) =[Ident ''head'']"
        by simp 
     have "?P e"
     proof(cut_tac a b1 b3,auto simp add:antOfRbFifo_def Let_def) qed
     (*fix s
     assume c1:" scalar2Bool (J 0 ''le'' [s (Ident ''head''), index 0])" 
     have "\<exists>i. ((s (Ident ''head'') ) = (index i))" 
        using headIsIndex by auto
     then obtain i where b1:"((s (Ident ''head'') ) = (index i))"
        by blast
     have b2:"i=0" 
        using a c1 b1 axiomOnLe  apply auto        done
     show "scalar2Bool (J 0 ''le'' [J 0 ''+'' [s (Ident ''head''), index (Suc 0)], index 0])"
      apply(cut_tac b1 b2,auto)
     done
     qed*)
     }
    moreover
    {assume b1:"e=Edge  ( Vertex 4) ( Vertex 1)"
     
     have b3:"varOfExp (applyPlusN head i) =[Ident ''head'']"
        by simp 
     have "?P e"
     proof(cut_tac a b1 b3,auto simp add:antOfRbFifo_def Let_def)
     qed
     }
    ultimately show "?P e" by satx
qed

lemma consistencyOfRbfifo:
  assumes a:"0 < LAST "
  shows "consistent' (ringBuffifo LAST ) (J LAST) (rbFifoGsteSpec LAST  data) 
  (tagFunOfRingBufFifo  data LAST)"
  proof(unfold consistent'_def,rule allI,rule impI)
    fix e
    let ?G=" (rbFifoGsteSpec LAST  data)"
    let ?M="(ringBuffifo LAST )"
    let ?tag="(tagFunOfRingBufFifo  data LAST)"
    let ?P ="\<lambda>e.   
    (let f=andListForm (?tag (sink e)) in
    let f'=andListForm (?tag (source e)) in
    tautlogy (implyForm (andForm f' (antOf ?G e)) (preCond1  f  ( ?M))) (J LAST))"
    
    assume a1:"e \<in> edgesOf (rbFifoGsteSpec LAST  data)"
    
    have "e=Edge vertexI ( Vertex 1) | 
          e=Edge  ( Vertex 1) ( Vertex 3) |
          e=Edge  ( Vertex 1) ( Vertex 4)|
           (\<exists>i. 0\<le>i \<and> i\<le> LAST+1 \<and>  e=( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) )   |
            (\<exists>i. 1\<le>i \<and> i\<le> LAST+1 \<and>  e=( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) |
            
           (\<exists>i. 1\<le>i \<and> i\<le> LAST  \<and> e=( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 3))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> LAST  \<and> e=( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 4))) )  |
           
           (\<exists>i. 0\<le>i \<and> i\<le> LAST  \<and>  e= ( Edge (Vertex (2 * i + 3))  (Vertex (2 * i + 1))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> LAST   \<and> e=( Edge (Vertex(2 * i + 4))  (Vertex(2 *i+ 2))))|
           e=Edge (Vertex 4) (Vertex 1)"
      (*apply(cut_tac a a1,auto)  done*) sorry
    moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac b1, simp add:antOfRbFifo_def)
     done
     }
    moreover
    {assume b1:" (\<exists>i. 0\<le>i \<and> i\<le> LAST+1  \<and>  e=( Edge (Vertex (2* i + 1))  (Vertex (  2*i + 1))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac b2, simp add:antOfRbFifo_def substNIl) done
    }
    moreover
    {assume b1:" (\<exists>i. 1\<le>i \<and> i\<le> LAST+1  \<and>  e=( Edge (Vertex (2* i + 2))  (Vertex (  2*i + 2))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac b2, simp add:antOfRbFifo_def substNIl) done
    }  
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 3) "
        
       let ?P' ="\<lambda>e.   
       (let f=andListForm (?tag (sink e)) in
       let f'=andListForm (?tag (source e)) in
       tautlogy (implyForm (andForm f' (antOf ?G e)) (preCond1  f  (branch2 LAST))) (J LAST))"
       
        let ?P1="\<lambda>e.   
       (let f=andListForm (?tag (sink e)) in
       let f'=andListForm (?tag (source e)) in
       let tailPlus=uif ''+'' [tail, (Const (index 1))] in
       let f1=andListForm [eqn tailPlus (applyPlusN head 1), eqn  LOW LOW,
         eqn full LOW, uip ''le'' [head,LASTE]] in
       tautlogy (implyForm (andForm f' (antOf ?G e)) f1) (J LAST))" 
       have c1:"?P e= ?P' e"
        by (simp add: a b1 del:tautlogy_def,auto)
       
      
      
        have "?P e "
       proof(cut_tac a b1,auto simp add:Let_def )  
       fix s i1
       assume c1:"0 <LAST" and c2:"Suc i1 mod Suc LAST = i1"
       show False
         apply(cut_tac c1 c2)
         by (metis mod_Suc mod_mod_trivial n_not_Suc_n neq0_conv old.nat.inject)
     qed
    }
    
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 4) "
      let ?f="andForm (neg (eqn rst HIGH)) (andForm (eqn push HIGH) nFullForm ) "
      have b2:"2*LAST +4 \<noteq> 4" apply(cut_tac a,arith) done
       have "?P e "
       proof(cut_tac a b1 b2,auto simp add:Let_def)
        fix s i1
       assume c1:"0 <LAST" and c2:"Suc i1 mod Suc LAST = i1"
       show False
         apply(cut_tac c1 c2)
         by (metis mod_Suc mod_mod_trivial n_not_Suc_n neq0_conv old.nat.inject)
     
     qed     
    }
    
    moreover
    {assume b1:" \<exists>i. 1\<le>i \<and> i \<le>LAST \<and> e=Edge  ( Vertex (2*i + 1)) ( Vertex (2*i + 3))"     (is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      have b2:"i - 1 < LAST" by(cut_tac a b1,auto)
      have b3:"varOfExp (applyPlusN head i) =[Ident ''head'']" by auto
      have "?P e "
      proof(cut_tac  a b1  b3 ,auto simp add: antOfRbFifo_def assms Let_def) 
        fix s i1
        assume  b1:" Suc 0 \<le> LAST" and
            b2:"Suc (if i1 = 0 then i1 + LAST else i1 + LAST - Suc LAST) mod Suc LAST \<noteq> i1"  and
            b3:"i1 \<le> LAST"  and b4:"i = LAST"
            
        show False 
          apply(cut_tac b1 b2 b3 )
          by (smt Suc_diff_Suc add_cancel_left_left add_diff_cancel_right' le_add2 mod_add_self2 nat_less_le test3)
      next
         fix s i1
        assume  b1:" Suc 0 \<le> i" and
            b2:"Suc (if i1 + i < Suc LAST then i1 + i else i1 + i - Suc LAST) mod Suc LAST = i1"  and
            b3:"i \<noteq> LAST"  and b4:"i1 \<le> LAST"  and b5:"i \<le> LAST"
        show False 
       
          
          apply(cut_tac a b1 b2 b3 b4 b5)
          by (smt Suc_diff_Suc add_cancel_left_left add_diff_cancel_left' 
              diff_diff_cancel less_Suc_eq mod_Suc mod_by_Suc_0 mod_if
              not_add_less1 not_le not_less_eq test4) 
      qed
     }
    
    moreover
    {assume b1:" \<exists>i. 1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 1)) ( Vertex (2*i+4))    "(is "\<exists>i. ?Q i")
     from b1 obtain i where b1:"?Q i" by blast
      have b2:"i - 1 < LAST" by(cut_tac a b1,auto)
      have b3:"varOfExp (applyPlusN head i) =[Ident ''head'']"
        by simp 
      have "i=LAST \<or> i <LAST" by(cut_tac b1 ,auto)
      moreover
      {assume b4:"i =LAST"        
      have "?P e "
      proof(cut_tac  a b1  b3 b4,auto simp add:  assms Let_def) 
        fix s i1
        assume  a1:"i = LAST" and
          a2:" Suc 0 \<le> LAST "  and a3:"i1 \<le> LAST "  and
          a4:"Suc (if i1 = 0 then i1 + LAST else i1 + LAST - Suc LAST) mod Suc LAST \<noteq> i1"
          
          
        show False  apply(cut_tac  a1  a1 a2 a3 a4 )
          by (smt Suc_diff_Suc add_cancel_left_left add_diff_cancel_right' le_add2 mod_add_self2 nat_less_le test3)
        
      next
         fix s i1
          assume  
          a4:"s (Ident ''tail'') =index (if i1 = 0 then i1 + LAST else i1 + LAST - Suc LAST) " and
          a2:"Suc (if i1 = 0 then i1 + LAST else i1 + LAST - Suc LAST) mod Suc LAST = i1 " and
          a3:"s (Ident ''dataIn'') = index data" and a5:"i1 \<le>  LAST" and a6:"i =LAST"  and
          a7:"s (Ident ''head'') = index i1 " and a8:" s (Ident ''tail'') = index (if i1 = 0 then i1 + LAST else i1 + LAST - Suc LAST)"
          
            
          
          have b3:"  
          expEval (J LAST)
          (substExp
            (caseExp (map (\<lambda>i. (eqn (applyPlusN head LAST) (Const (index i)), IVar (Para mem i))) (down LAST)))
            (map (\<lambda>i. (Para mem i,
                       iteForm (eqn tail (Const (index i))) dataIn (IVar (Para mem i))))
              (down LAST)))
          s =
         expEval (J LAST) dataIn s" thm auxOnReadWrite 
            apply(rule_tac e'="applyPlusN head LAST" and e="tail" and i="(if i1 = 0 then i1 + LAST else i1 + LAST - Suc LAST)" in readWrite)
            apply(cut_tac b4 a2 a3 a4 a5 a6 a7 a8,simp)   
              apply(cut_tac b4 a2 a3 a4 a5 a6 a7 a8,simp) 
            apply(cut_tac a5,arith)
            by auto
         
          show "
          expEval (J LAST)
          (substExp
            (caseExp (map (\<lambda>i. (eqn (applyPlusN head LAST) (Const (index i)), IVar (Para mem i))) (down LAST)))
            (map (\<lambda>i. (Para mem i,
                       iteForm (eqn tail (Const (index i))) dataIn (IVar (Para mem i))))
              (down LAST)))
          s =
         index data"
          using a3 b3  by auto
      qed 
      }
      moreover
      {assume b4:" i <LAST" 
      have "?P e "
      proof(cut_tac  a b1 b3 b4,auto simp add: antOfRbFifo_def assms Let_def)   
        fix s i1
        assume  
          a4:" Suc (if i1 + i < Suc LAST then i1 + i else i1 + i - Suc LAST) mod Suc LAST = i1 "
          and a1:"i < LAST" and a2:"Suc 0 \<le> i"  and a3:"i1 \<le>LAST"
          
        show False
          apply(cut_tac a1 a2 a3 a4)
          by (smt Suc_diff_Suc Suc_le_lessD add_cancel_left_left add_diff_cancel_left' assms diff_diff_cancel lessI mod_Suc mod_if nat_less_le not_add_less1 not_le test4)
         
        
      next
        
        fix s i1
         assume  
          a4:"s (Ident ''tail'') = index (if i1 + i < Suc LAST then i1 + i else i1 + i - Suc LAST) " and
          a3:"s (Ident ''dataIn'') = index data" and a5:"i1 \<le>  LAST" and a6:"i <LAST"   and a8:"s (Ident ''head'') = index i1 "
          have b5:"expEval (J LAST)
          (substExp
            (caseExp (map (\<lambda>i'. (eqn (applyPlusN head i) (Const (index i')), IVar (Para mem i'))) (down LAST)))
            (map (\<lambda>i'. (Para mem i',
                       iteForm (eqn tail (Const (index i'))) dataIn (IVar (Para mem i'))))
              (down LAST)))
          s =
         expEval (J LAST) dataIn s"
            apply(rule_tac e'="applyPlusN head i" and e="tail" and i="(if i1 + i < Suc LAST then i1 + i else i1 + i - Suc LAST)" in readWrite)
            apply(cut_tac  a4 a5 a6  a8,simp)   
            using a4 apply simp
              apply (simp add: a4)
            using a5 b4 apply linarith
            by auto    
          show " expEval (J LAST)
             (substExp (caseExp (map (\<lambda>ia. (eqn (applyPlusN head i) (Const (index ia)), IVar (Para mem ia))) (down LAST)))
               (map (\<lambda>i. (Para mem i, iteForm (eqn tail (Const (index i))) dataIn (IVar (Para mem i)))) (down LAST)))
             s =
            index data "
          using a3 b5  by auto
      qed 

      
      }
      ultimately have "?P e " by satx
       
     } 
    
     moreover
    {assume b1:"\<exists>i. 0\<le>i \<and> i\<le> LAST \<and>  e=Edge  ( Vertex (2*i + 3)) ( Vertex (2*i + 1))   " (is "\<exists>i. ?Q i")
       from b1 obtain i where b1:"?Q i" by blast
      have b2:"i - 1 < LAST" by(cut_tac a b1,auto)
      have b3:"varOfExp (applyPlusN head i) =[Ident ''head'']"
        by simp 
      
      have "i=LAST \<or> i <LAST" by(cut_tac b1 ,auto)
      moreover
      {assume b4:"i =LAST"        
      have "?P e "
      proof(cut_tac  a b1  b3 b4,auto simp add:  assms Let_def)
        fix s i1
        assume c1:"i = LAST" and c2:"
            Suc (if i1 = 0 then i1 + LAST else i1 + LAST - Suc LAST) mod Suc LAST = Suc i1 mod Suc LAST"
            and c3:"i1 \<le> LAST"
        show False
          apply(cut_tac c1 c2 c3)
        proof -
          assume "i = LAST"
          have "\<not> LAST < LAST + i1 \<or> i1 = 0 \<or> Suc i1 mod Suc LAST = i1 mod Suc LAST"
            using c2 by force
          then have f1: "0 = i1"
            by (metis (no_types) Suc_le_eq add.commute add_diff_cancel_left' assms cancel_comm_monoid_add_class.diff_cancel le_add2 mod_Suc n_not_Suc_n nat_less_le)
          then have "i1 mod Suc LAST = 1 mod Suc LAST"
            using c2 by force
          then show ?thesis
            using f1 by (metis One_nat_def Suc_le_eq assms mod_Suc n_not_Suc_n nat_less_le)
        qed
      next
        fix s
        assume c1:" i = LAST" and c2:" s (Ident ''head'') = index 0"
        show " index 0 = expEval (J LAST) (substExp (applyPlusN head LAST) [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])]) s"
          sorry
      next
        fix s i1
        show " index i1 = expEval (J LAST) (substExp (applyPlusN head LAST) [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])]) s"
          sorry
      qed    
     }
     moreover
      {assume b4:"i <LAST"        
      have "?P e "
      proof(cut_tac  a b1  b3 b4,auto simp add:  assms Let_def) 
      fix s
      have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
            using headIsIndex by auto
          then obtain j where b1:"((s (Ident ''head'') ) = (index j))"
            by blast  
      show "scalar2Bool (J LAST ''le'' [J LAST ''+'' [s (Ident ''head''), index (Suc 0)], index LAST])"
        apply(cut_tac b1,auto) done
     
     next
      fix s
      assume c1:" J LAST ''+'' [expEval (J LAST) (applyPlusN head i) s, index (Suc 0)] =
      J LAST ''+'' [s (Ident ''head''), index (Suc 0)]" and 
      c2:" scalar2Bool (J LAST ''le'' [s (Ident ''head''), index LAST])" and c3:"0<i"
       have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
            using headIsIndex by auto
          then obtain j where e1:"((s (Ident ''head'') ) = (index j))"
            by blast 
        have e2:"j\<le> LAST" 
          using  c2 e1 axiomOnLe  apply auto        done thm  onApplyPlusI
        have e3:"expEval (J LAST) (applyPlusN head i) s= index ((j +i) mod Suc LAST)"
          by (simp add: e1 e2 b4 less_imp_le_nat)
          
        show False
       apply(cut_tac a b1 e1 e2 e3 c1 c3, simp)
       by (smt Divides.mod_less le_imp_less_Suc le_mod_geq mod_Suc nat.distinct(1) nat.inject neq0_conv not_less test5)
     next
      fix s
      have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
            using headIsIndex by auto
          then obtain j where b1:"((s (Ident ''head'') ) = (index j))"
            by blast  
      show " scalar2Bool (J LAST ''le'' [J LAST ''+'' [s (Ident ''head''), index (Suc 0)], index LAST])"
        apply(cut_tac b1,auto) done
     next
      fix s
        show "J LAST ''+'' [expEval (J LAST) (applyPlusN head i) s, index (Suc 0)] =
         expEval (J LAST) (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) i) s"
         by (simp add: applyIPlusIsPlusI)
    qed
    }
   ultimately have "?P e " by satx
   }
  
  
     moreover
    {assume b1:"\<exists>i.  1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 4)) ( Vertex (2*i+2 ))   " (is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      
      have b3:"varOfExp (applyPlusN head i) =[Ident ''head'']"
        by simp 
      have "i=LAST \<or> i <LAST" by(cut_tac b1 ,auto)
      moreover
      {assume b4:"i =LAST"        
      have "?P e "
      proof(cut_tac  a b1  b3 b4,auto simp add:  assms Let_def)
        fix s

        assume c1:" J LAST ''+'' [expEval (J LAST) (applyPlusN head LAST) s, index (Suc 0)] = 
        J LAST ''+'' [s (Ident ''head''), index (Suc 0)]" and 
        c2:" scalar2Bool (J LAST ''le'' [s (Ident ''head''), index LAST])" 
        have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
            using headIsIndex by auto
        then obtain j where e1:"((s (Ident ''head'') ) = (index j))"
            by blast 
        have e2:"j\<le> LAST" 
          using  c2 e1 axiomOnLe  apply auto        done thm  onApplyPlusI
        have e3:"J LAST ''+'' [expEval (J LAST) (applyPlusN head LAST) s, index (Suc 0)]= index j"
          by (metis c2 e1 iPlusSucLatIsi)
          
        have e4:"J LAST ''+'' [s (Ident ''head''), index (Suc 0)] = index ((j +1) mod Suc LAST) "
          by (simp add: e1)
        show False
          apply(cut_tac c1 e3 e4 a, simp)
          by (metis e1 iPlus1IsNotI)
      next
        fix s
        show "  J LAST ''+'' [expEval (J LAST) (applyPlusN head LAST) s, index (Suc 0)] =
          expEval (J LAST) (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) LAST) s"
          using applyIPlusIsPlusI by auto
      next
        fix s
        
          have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
            using headIsIndex by auto
          then obtain j where b1:"((s (Ident ''head'') ) = (index j))"
            by blast  
          show "scalar2Bool (J LAST ''le'' [J LAST ''+'' [s (Ident ''head''), index (Suc 0)], index LAST])"
          apply(cut_tac b1,auto) done
      next
        fix s
        assume  
          a2:" scalar2Bool (J LAST ''le'' [s (Ident ''head''), index LAST])" and 
          a4:"expEval (J LAST) (caseExp (map (\<lambda>i. (eqn (applyPlusN head LAST) (Const (index i)), IVar (Para mem i))) (down LAST))) s =
         index data"
          have "\<exists>i. ((s (Ident ''head'') ) = (index i))" 
          using headIsIndex by auto
          then obtain j where b1:"((s (Ident ''head'') ) = (index j))"
          by blast
          have b2:"j\<le> LAST" 
          using  a2 b1 axiomOnLe  apply auto        done
          (*have a0:"s (Ident ''tail'') = s (Ident ''head'')"*)
          have b20:"tautlogy (eqn (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (LAST - Suc 0)) 
                              (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (LAST - Suc 0))) (J LAST)"
                  apply(induct_tac LAST, auto) done
          have b3:"  
          expEval (J LAST)
          (substExp
            (caseExp
              (map (\<lambda>i. (eqn (applyPlusN head (LAST - Suc 0)) (Const (index i)), IVar (Para mem i))) (down LAST)))
            [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])])
          s   =
           expEval (J LAST)
          (caseExp
            (map (\<lambda>i. (eqn (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (LAST - Suc 0)) (Const (index i)), IVar (Para mem i)))
            (down LAST))) s" 
            using substCaseExp1 by auto

         have b4:" expEval (J LAST)
          ((caseExp (map (\<lambda>i. (eqn (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (LAST - Suc 0)) (Const (index i)), 
          IVar (Para mem i))) (down LAST)))
            )
          s =
         expEval (J LAST) (caseExp (map (\<lambda>i. (eqn (applyPlusN head LAST) (Const (index i)), IVar (Para mem i))) (down LAST))) s"
         proof(rule caseExpCong1,simp)
            
            
            have "\<exists>i. ((s (Ident ''head'') ) = (index i))" 
            using headIsIndex by auto
            then obtain j where b1:"((s (Ident ''head'') ) = (index j))"
              by blast
            have b2:"j\<le> LAST" 
            using  a2 b1 axiomOnLe  apply auto        done
            show "expEval (J LAST) (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (LAST - Suc 0)) s
            = expEval (J LAST) (applyPlusN head LAST) s"
            apply(cut_tac a b1 b2,auto) done
          qed
         
          show "expEval (J LAST)
          (substExp (caseExp (map (\<lambda>i. (eqn (applyPlusN head (LAST - Suc 0)) (Const (index i)), IVar (Para mem i))) (down LAST)))
            [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])])
          s =
         index data"
         by (simp add: a4 b3 b4)
        
      qed     
     }
    moreover
    {assume b4:"i <LAST"        
      have "?P e "
      proof(cut_tac  a b1  b3 b4,auto simp add:  assms Let_def) 
      fix s
      have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
            using headIsIndex by auto
          then obtain j where b1:"((s (Ident ''head'') ) = (index j))"
            by blast  
      show "scalar2Bool (J LAST ''le'' [J LAST ''+'' [s (Ident ''head''), index (Suc 0)], index LAST])"
        apply(cut_tac b1,auto) done
     
     next
      fix s
      assume c1:" J LAST ''+'' [expEval (J LAST) (applyPlusN head i) s, index (Suc 0)] =
      J LAST ''+'' [s (Ident ''head''), index (Suc 0)]" and 
      c2:" scalar2Bool (J LAST ''le'' [s (Ident ''head''), index LAST])" and c3:"Suc 0 \<le> i"
       have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
            using headIsIndex by auto
          then obtain j where e1:"((s (Ident ''head'') ) = (index j))"
            by blast 
        have e2:"j\<le> LAST" 
          using  c2 e1 axiomOnLe  apply auto        done thm  onApplyPlusI
        have e3:"expEval (J LAST) (applyPlusN head i) s= index ((j +i) mod Suc LAST)"
          by (simp add: e1 e2 b4 less_imp_le_nat)
          
        show False
       apply(cut_tac a b1 e1 e2 e3 c1 c3, simp)
       by (smt Divides.mod_less le_imp_less_Suc le_mod_geq mod_Suc nat.distinct(1) nat.inject neq0_conv not_less test5)
     next
      fix s
      assume d1:"i <LAST" and d2:"Suc 0 \<le> i"
        show "J LAST ''+'' [expEval (J LAST) (applyPlusN head i) s, index (Suc 0)] =
         expEval (J LAST) (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) i) s"
         by (simp add: applyIPlusIsPlusI)
      next
       fix s
        assume  
          a1:"Suc 0 \<le> i" and
          a2:" scalar2Bool (J LAST ''le'' [s (Ident ''head''), index LAST])" and 
          a4:"expEval (J LAST) (caseExp (map (\<lambda>ia. (eqn (applyPlusN head i) (Const (index ia)), IVar (Para mem ia))) (down LAST))) s =
         index data"
          have "\<exists>i. ((s (Ident ''head'') ) = (index i))" 
          using headIsIndex by auto
          then obtain j where b1:"((s (Ident ''head'') ) = (index j))"
          by blast
          have b2:"j\<le> LAST" 
          using  a2 b1 axiomOnLe  apply auto        done
          (*have a0:"s (Ident ''tail'') = s (Ident ''head'')"*)
          have b20:"tautlogy (eqn (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (LAST - Suc 0)) 
                              (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (LAST - Suc 0))) (J LAST)"
                  apply(induct_tac LAST, auto) done
          have b3:"  
          expEval (J LAST)
          (substExp
            (caseExp
              (map (\<lambda>ia. (eqn (applyPlusN head (i - Suc 0)) (Const (index ia)), IVar (Para mem ia))) (down LAST)))
            [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])])
          s   =
           expEval (J LAST)
          (caseExp
            (map (\<lambda>ia. (eqn (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (i - Suc 0)) (Const (index ia)), IVar (Para mem ia)))
            (down LAST))) s" 
            using substCaseExp1 by auto

         have c4:" expEval (J LAST)
          ((caseExp (map (\<lambda>ia. (eqn (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (i - Suc 0)) (Const (index ia)), 
          IVar (Para mem ia))) (down LAST)))
            )
          s =
         expEval (J LAST) (caseExp (map (\<lambda>ia. (eqn (applyPlusN head i) (Const (index ia)), IVar (Para mem ia))) (down LAST))) s"
         proof(rule caseExpCong1,simp)
            
            
            have "\<exists>i. ((s (Ident ''head'') ) = (index i))" 
            using headIsIndex by auto
            then obtain j where b1:"((s (Ident ''head'') ) = (index j))"
              by blast
            have b2:"j\<le> LAST" 
            using  a2 b1 axiomOnLe  apply auto        done
            show "expEval (J LAST) (applyPlusN (uif ''+'' [head, Const (index (Suc 0))]) (i - Suc 0)) s
            = expEval (J LAST) (applyPlusN head i) s"
            apply(cut_tac a b1 b2 b4 a1,auto)
            done
          qed
         
          show "expEval (J LAST)
          (substExp (caseExp (map (\<lambda>ia. (eqn (applyPlusN head (i - Suc 0)) (Const (index ia)), IVar (Para mem ia))) (down LAST)))
            [(Ident ''head'', uif ''+'' [head, Const (index (Suc 0))])])
          s =
         index data"
         by (simp add: a4 b3 c4)
        
      qed 
    }
    ultimately have "?P e" by satx
    }
    moreover
    {assume b1:"e=Edge (Vertex 4) ( Vertex 1)"
     have "?P e"
     proof(cut_tac a b1, simp add:antOfRbFifo_def Let_def,auto)
     fix s
     assume c2:" scalar2Bool (J LAST ''le'' [s (Ident ''head''), index LAST])"
       have "\<exists>i. ((s (Ident ''head'') ) = (index i))"
            using headIsIndex by auto
          then obtain j where e1:"((s (Ident ''head'') ) = (index j))"
            by blast 
        have e2:"j\<le> LAST"
         using  c2 e1 axiomOnLe  apply auto        done 
        show " scalar2Bool (J LAST ''le'' [J LAST ''+'' [s (Ident ''head''), index (Suc 0)], index LAST]) "
        apply(cut_tac e1 e2,auto) done
     qed
     }
ultimately show "?P e" by satx
qed  
lemma testAux[simp]:
 
shows "(expEval I e s =index i \<longrightarrow>
i \<le> LAST\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)), me i)) (down LAST)@S))) s 
=expEval  I  (me i) s) \<and>
(expEval I e s =index i \<longrightarrow>
 LAST < i\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)),me i)) (down LAST)@S))) s 
=expEval  I  (caseExp S) s)"  (is "?P LAST")
proof(induct_tac LAST,auto )qed 

lemma test[simp]:
shows "(expEval I e s =index i \<longrightarrow>
i \<le> LAST\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)), me i)) (down LAST)))) s 
=expEval  I  (me i) s)"
proof -
have a:"(expEval I e s =index i \<longrightarrow>
i \<le> LAST\<longrightarrow>expEval I (caseExp ((map (\<lambda>i. (eqn e (Const (index i)), me i)) (down LAST)@[]))) s 
=expEval  I  (me i) s)"
apply(cut_tac testAux  [where I="I" and S="[]" and i="i" and e="e" and s="s" and LAST="LAST" and me="me"]) 
apply simp
done
then show ?thesis by auto
qed

 

lemma instImply:
assumes a:"G=(rbFifoGsteSpec LAST  data)"   and c:"tag=tagFunOfRingBufFifo  data LAST"
shows
"\<forall> e. e \<in>edgesOf G\<longrightarrow> 
tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) I"  
proof(rule allI,rule impI,simp,rule allI,rule impI)
  fix e s
  assume a1:"e \<in> edgesOf G " and a2:"
           formEval I (antOf G e) s \<and> formEval I (andListForm (tag (source e))) s" 
  let ?P ="\<lambda>e. formEval I (consOf G e) s"           
  have "e=Edge vertexI ( Vertex 1) | 
          e=Edge  ( Vertex 1) ( Vertex 3) |
          e=Edge  ( Vertex 1) ( Vertex 4)|
           (\<exists>i. 0\<le>i \<and> i\<le> LAST+1 \<and>  e=( Edge (Vertex ( 2*i+1 ))  (Vertex (  2*i+1 ))) )   |
            (\<exists>i. 1\<le>i \<and> i\<le> LAST+1 \<and>  e=( Edge (Vertex ( 2*i+2 ))  (Vertex (  2*i+2 ))) ) |
            
           (\<exists>i. 1\<le>i \<and> i\<le> LAST  \<and> e=( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 3))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> LAST  \<and> e=( Edge (Vertex (2 * i + 1))  (Vertex (2 * i + 4))) )  |
           
           (\<exists>i. 0\<le>i \<and> i\<le> LAST  \<and>  e= ( Edge (Vertex (2 * i + 3))  (Vertex (2 * i + 1))) ) |
           (\<exists>i. 1\<le>i \<and> i\<le> LAST   \<and> e=( Edge (Vertex(2 * i + 4))  (Vertex(2 *i+ 2))))|
           e=Edge (Vertex 4) (Vertex 1)"
      apply(cut_tac a a1,auto)  done
     
   
    moreover
    {assume b1:"e=Edge vertexI ( Vertex 1)"
     have "?P e"
     apply(cut_tac a b1, simp add:antOfRbFifo_def) done
     }
    moreover
    {assume b1:" (\<exists>i. 0\<le>i \<and> i\<le> LAST +1  \<and>  e=( Edge (Vertex (2* i + 1))  (Vertex (  2*i + 1))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac a  c a2 b2, auto) done
    }
    moreover
    {assume b1:" (\<exists>i. 1\<le>i \<and> i\<le> LAST+1  \<and>  e=( Edge (Vertex (2* i + 2))  (Vertex (  2*i + 2))) )  " (is "\<exists>i. ?asm i")
     from b1 obtain i where b2:"?asm i" by auto
      have "?P e"
       apply(cut_tac  a  c a2 b2,auto) done
    }  
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 3) "
    
       have "?P e"
        apply(cut_tac a  c a2 b1,auto ) done
    }
    
     moreover
    {assume b1:" e=Edge  ( Vertex 1) ( Vertex 4) "
      let ?f="andForm (neg (eqn rst HIGH)) (andForm (eqn push HIGH) (neg (eqn tail (Const (index LAST )))) ) "
     
     
       have "?P e "
        apply(cut_tac a a1 a2 b1 ,auto simp add: antOfRbFifo_def assms) done
    }
    
    moreover
    {assume b1:" \<exists>i. 1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 1)) ( Vertex (2*i + 3))"     (is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      have "?P e "
        by(cut_tac  a  c a2 b1 ,auto simp add: antOfRbFifo_def assms )
     }
    
    moreover
    {assume b1:" \<exists>i. 1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 1)) ( Vertex (2*i+4))    "(is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      have "?P e "
        by(cut_tac a b1 a1 a2,auto simp add: antOfRbFifo_def assms)
     } 
    
     moreover
    {assume b1:"\<exists>i. 0\<le>i \<and> i\<le> LAST \<and>  e=Edge  ( Vertex (2*i + 3)) ( Vertex (2*i + 1))   " (is "\<exists>i. ?Q i")
       from b1 obtain i where b1:"?Q i" by blast
       have "?P e "
        by(cut_tac   a  c a2 b1 ,auto simp add:Let_def antOfRbFifo_def assms )
     }
    
     moreover
    {assume b1:"\<exists>i.  1\<le>i \<and> i\<le> LAST \<and> e=Edge  ( Vertex (2*i + 4)) ( Vertex (2*i +2))   " (is "\<exists>i. ?Q i")
      from b1 obtain i where b1:"?Q i" by blast
      have "?P e "
         by(cut_tac  a   a2 b1 ,auto simp add: Let_def antOfRbFifo_def assms)
       
     }
    moreover
    {assume b1:"e=Edge (Vertex 4) ( Vertex 1)"
     have "?P e"
     apply(cut_tac  a  c a2 b1 ,case_tac "LAST=0",auto  simp add: Let_def antOfRbFifo_def assms) done
     }
    ultimately show "?P e" by satx
  qed      

lemma main: 
assumes a:"G=(rbFifoGsteSpec LAST  data)" 
and c:"tag=tagFunOfRingBufFifo  data LAST" and
d:"M=(ringBuffifo  LAST )"
shows " circuitSatGsteSpec M G (J LAST) "  
proof(rule mainLemma)
have a1:"consistent' (ringBuffifo LAST ) (J LAST) (rbFifoGsteSpec LAST  data) (tagFunOfRingBufFifo  data LAST)" 
   apply (case_tac "LAST=0",rule consistencyOfRbfifo0,simp)
   apply(rule   consistencyOfRbfifo,arith) done
from a c d this show "consistent' M   (J LAST) G tag"
  by simp   
next
from a  c show "\<forall>e. e \<in> edgesOf G \<longrightarrow>
        tautlogy (implyForm (andForm (antOf G e) (andListForm (tag (source e)))) (consOf G e)) (J LAST)"
apply(rule instImply) done
next
from a c show "tag (initOf G) = []"
apply auto done
qed
end
