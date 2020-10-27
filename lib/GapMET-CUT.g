#
# By convention, we write the distance vectors as
# (p, d_12, ...., d_1n, d_23, ..., d_2n, d_34, ..., d_3n, ..., d_n-1 n)
# with p=0 for cut cone and p=1 for cut polytope.

#
# the distance matrix is a symmetric nxn matrix with on place i,j
# the value d(i,j).

FromHypermetricVectorToHypermetricFace:=function(HypV)
  local HypDim, V, i, j, S, k, iCol;
  HypDim:=Length(HypV);
  S:=Sum(HypV);
  k:=(S-1)/2;
  V:=[k*(k+1)];
  #
  for i in [1..HypDim-1]
  do
    for j in [i+1..HypDim]
    do
      Add(V, -HypV[i]*HypV[j]);
    od;
  od;
  return V;
end;



DistanceVectorToDistanceMatrix:=function(d, nbVert)
  local idx, iCol, iLin, DistMat;
  DistMat:=NullMat(nbVert,nbVert);
  idx:=2;
  for iCol in [1..nbVert-1]
  do
    for iLin in [iCol+1..nbVert]
    do
      DistMat[iCol][iLin]:=d[idx];
      DistMat[iLin][iCol]:=d[idx];
      idx:=idx+1;
    od;
  od;
  return DistMat;
end;


#
#
# return a distance vector with first component equal to 0.
DistanceMatrixToDistanceVector:=function(DistMat)
  local d, nbVert, i, j;
  d:=[0];
  nbVert:=Length(DistMat);  
  for i in [1..nbVert-1]
  do
    for j in [i+1..nbVert]
    do
      Add(d, DistMat[i][j]);
    od;
  od;
  return d;
end;









#
#
# return the hypermetric symbols for
# triangle facets
# type can be "polytope" or "cone"
SpanMETsymbol:=function(n, type)
  local H, V, SymbSet, u, R;
  if type<>"polytope" and type<>"cone" then
    return fail;
  fi;
  V:=ListWithIdenticalEntries(n, 0);
  SymbSet:=[];
  for u in Combinations([1..n], 3)
  do
    R:=ShallowCopy(V);
    R[u[1]]:=-1; R[u[2]]:=1; R[u[3]]:=1;
    Add(SymbSet, R);
    #
    R:=ShallowCopy(V);
    R[u[1]]:=1; R[u[2]]:=-1; R[u[3]]:=1;
    Add(SymbSet, R);
    #
    R:=ShallowCopy(V);
    R[u[1]]:=1; R[u[2]]:=1; R[u[3]]:=-1;
    Add(SymbSet, R);
    #
    if type="polytope" then
      R:=ShallowCopy(V);
      R[u[1]]:=1; R[u[2]]:=1; R[u[3]]:=1;
      Add(SymbSet, R);
    fi;
  od;
  return SymbSet;
end;



#
#
# return the graph if d is the distance vector
# of a graph and false otherwise
DistanceVectorToGraph:=function(d, nbVert)
  local DistMat, Gra, i, j;
  DistMat:=DistanceVectorToDistanceMatrix(d, nbVert);
  Gra:=NullGraph(Group(()), nbVert);
  for i in [1..nbVert]
  do
    for j in [1..nbVert]
    do
      if i<>j and DistMat[i][j]=1 then
        AddEdgeOrbit(Gra, [i,j]);
      fi;
    od;
  od;
  for i in [1..nbVert]
  do
    for j in [1..nbVert]
    do
      if Distance(Gra, i, j)<> DistMat[i][j] then
        return false;
      fi;
    od;
  od;
  return Gra;
end;




IsConflicting:=function(eTrig, fTrig)
  local iCol;
  for iCol in [1..Length(eTrig)]
  do
    if eTrig[iCol]*fTrig[iCol]<0 then
      return true;
    fi;
  od;
  return false;
end;




#
#
# return the group Sym(n) of permutation on 2-uples
MET_Group:=function(G,n)
   local SS2, i, j;
   SS2:=[[1..n]];
   for i in [1..n-1]
   do
     for j in [i+1..n]
     do
       Add(SS2, Set([i,j]));
     od;
   od;
   return TranslateGroup(G, SS2, OnSets);
end;

#
#
# type can be "cone" or "polytope"
MET_Facets:=function(n, type)
  local VZ, i,j,k, SS2, Fac, FacList, Pos1, Pos2, Pos3;
  SS2:=[[1..n]];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(SS2, Set([i,j]));
    od;
  od;
  VZ:=ListWithIdenticalEntries(n*(n-1)/2+1, 0);
  FacList:=[];
  for i in [1..n-2]
  do
    for j in [i+1..n-1]
    do
      for k in [j+1..n]
      do
	Pos1:=Position(SS2, [i,j]);
	Pos2:=Position(SS2, [i,k]);
	Pos3:=Position(SS2, [j,k]);
	Fac:=ShallowCopy(VZ);
	Fac[Pos1]:=1;
	Fac[Pos2]:=1;
	Fac[Pos3]:=-1;
	Add(FacList, Fac);
	Fac:=ShallowCopy(VZ);
	Fac[Pos1]:=1;
	Fac[Pos2]:=-1;
	Fac[Pos3]:=1;
	Add(FacList, Fac);
	Fac:=ShallowCopy(VZ);
	Fac[Pos1]:=-1;
	Fac[Pos2]:=1;
	Fac[Pos3]:=1;
	Add(FacList, Fac);
	if type="polytope" then
	  Fac:=ShallowCopy(VZ);
	  Fac[1]:=2;
	  Fac[Pos1]:=-1;
	  Fac[Pos2]:=-1;
	  Fac[Pos3]:=-1;
	  Add(FacList, Fac);
	fi;
      od;
    od;
  od;
  return FacList;
end;



DressPairsFacet:=function(n, ListPair)
  local ePair, ListV, i, j, x, y, u, v, V, ListInequation;
  ListV:=[];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(ListV, [i,j]);
    od;
  od;
  ListInequation:=[];
  for ePair in ListPair
  do
    x:=ePair[1][1];
    y:=ePair[1][2];
    u:=ePair[2][1];
    v:=ePair[2][2];
    V:=[];
    for i in [1..Length(ListV)+1]
    do
      Add(V, 0);
    od;
    V[Position(ListV, Set([x,y]))+1]:=1;
    V[Position(ListV, Set([u,v]))+1]:=1;
    V[Position(ListV, Set([x,u]))+1]:=-1;
    V[Position(ListV, Set([y,v]))+1]:=-1;
    Add(ListInequation, ShallowCopy(V));
    V[Position(ListV, Set([x,u]))+1]:=0;
    V[Position(ListV, Set([y,v]))+1]:=0;
    V[Position(ListV, Set([x,v]))+1]:=-1;
    V[Position(ListV, Set([y,u]))+1]:=-1;
    Add(ListInequation, ShallowCopy(V));
  od;
  return ListInequation;
end;


#
# SET is a 0/1 vector
# option can be "vertex" or "extreme"
FromCutToCutVector:=function(SET, option)
  local n, u, V, i, j;
  n:=Length(SET);
  if option="extreme" then
    V:=[0];
  elif option="vertex" then
    V:=[1];
  else
    return false;
  fi;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
	if SET[i]+SET[j]=1 then
	  Add(V, 1);
	else
	  Add(V, 0);
	fi;
    od;
  od;
  return V;
end;





#
#
# type can be "vertex" or "extreme"
CUT_Vertex:=function(n,type)
  local DO, iDO, LEXT, SET, LSET;
  DO:=BuildSet(n-1,[0,1]);
  if type="extreme" then
    DO:=Difference(DO,[ListWithIdenticalEntries(n-1, 0)]);
  fi;
  LEXT:=[];
  LSET:=[];
  for iDO in [1..Length(DO)]
  do
    SET:=DO[iDO];
    SET[n]:=0;
    Add(LEXT, FromCutToCutVector(SET, type));
    Add(LSET, SET);
  od;
  return rec(EXT:=LEXT, SET:=LSET);
end;



#
# SET must be a 0/1 sequence
# type can be "vertex" or "facet"
Switching:=function(SET, Object, type)
  local VZ, VECT, i, S;
  VZ:=FromCutToCutVector(SET, "extreme");
  VECT:=[];
  if type="vertex" then
    VECT[1]:=Object[1];
    for i in [2..Length(Object)]
    do
      if VZ[i]=1 then
	VECT[i]:=Object[1]-Object[i];
      else
	VECT[i]:=Object[i];
      fi;
    od;
  else
    S:=Object[1];
    for i in [2..Length(Object)]
    do
      if VZ[i]=1 then
	S:=S+Object[i];
      fi;
    od;
    VECT[1]:=S;
    for i in [2..Length(Object)]
    do
      if VZ[i]=1 then
	VECT[i]:=-Object[i];
      else
	VECT[i]:=Object[i];
      fi;
    od;
  fi;
  return VECT;
end;




#
# We consider here the group formed by permutations on the 
# n variables together with switching
# type can be "vertex" or "facet"
TotalGroup:=function(OBJ, n, type)
  local Gn, SET, iElt, Gens, L, U;
  Gn:=MET_Group(SymmetricGroup([1..n]),n);
  SET:=ListWithIdenticalEntries(n, 0);
  SET[1]:=1;
  L:=[];
  for iElt in [1..Length(OBJ)]
  do
    L[iElt]:=Position(OBJ, Switching(SET, OBJ[iElt], type));
  od;
  Gens:=GeneratorsOfGroup(TranslateGroup(Gn, OBJ, Permuted));
  U:=ShallowCopy(Gens);
  Add(U, PermList(L));
  return Group(U);
end;








TestAdj:=function(Symb1, Symb2)
  local Pos1, Pos2f, Pos2s;
  Pos1:=Position(Symb1, -1);
  Pos2f:=Position(Symb1, 1);
  Pos2s:=Position(Symb1, 1, Pos2f);
  if Symb2[Pos2f]*Symb2[Pos2s]=-1 then
    return false;
  fi;
  if Symb2[Pos1]=1 and Symb2[Pos2f]=1 then
    return false;
  fi;
  if Symb2[Pos1]=1 and Symb2[Pos2s]=1 then
    return false;
  fi;
  return true;
end;

#
#
# there are three types of non-adjacent facets in MET
TripleOrbit:=function(n)
  local V1, V2, V3, ListTriple;
  ListTriple:=[];
  V1:=ListWithIdenticalEntries(n, 0);
  V2:=ListWithIdenticalEntries(n, 0);
  V3:=ListWithIdenticalEntries(n, 0);
  V1[1]:=1;  V1[2]:=1;  V1[3]:=-1;
  V2[1]:=1;  V2[2]:=-1; V2[3]:=1;
  V3[1]:=-1; V3[2]:=1;  V3[3]:=1;
  Add(ListTriple, [ShallowCopy(V1),ShallowCopy(V2),ShallowCopy(V3)]);
  if n >= 4 then
    V1[1]:=1; V1[2]:=1;  V1[3]:=-1;
    V2[1]:=1; V2[2]:=-1; V2[3]:=1;
    V3[2]:=1; V3[3]:=1;  V3[4]:=-1;
    Add(ListTriple, [ShallowCopy(V1),ShallowCopy(V2),ShallowCopy(V3)]);
  fi;
  if n >= 4 then
    V1[1]:=1; V1[2]:=1; V1[3]:=-1;
    V2[1]:=1; V2[2]:=-1; V2[4]:=1;
    V3[1]:=1; V3[3]:=1; V3[4]:=-1;
    Add(ListTriple, [ShallowCopy(V1),ShallowCopy(V2),ShallowCopy(V3)]);
  fi;
  return ListTriple;
end;


CommonNonAdj:=function(triple, FacSet)
  local OneNonAdj, TwoNonAdj, t1, t2, t3, nb, u;
  OneNonAdj:=0;
  TwoNonAdj:=0;
  for u in FacSet
  do
    t1:=TestAdj(triple[1], u);
    t2:=TestAdj(triple[2], u);
    t3:=TestAdj(triple[3], u);
    nb:=0;
    if t1=false then 
	nb:=nb+1;
    fi;
    if t2=false then 
	nb:=nb+1;
    fi;
    if t3=false then 
	nb:=nb+1;
    fi;
    if nb=1 then 
	OneNonAdj:=OneNonAdj+1;
    fi;
    if nb=2 then 
	TwoNonAdj:=TwoNonAdj+1;
    fi;
  od;
  return [OneNonAdj, TwoNonAdj];
end;


FCT:=function(n,type)
  return CommonNonAdj(TripleOrbit(n)[type], Difference(SpanMETsymbol(n), TripleOrbit(n)[type]));
end;





#
# Cut is a 0/1 vector with first coordinate equal to 0
CutAction:=function(Cut, g)
  local CC, DD, iCol;
  CC:=Permuted(Cut,g);
  if CC[1]=1 then
    DD:=[];
    for iCol in [1..Length(CC)]
    do
      DD[iCol]:=1-CC[iCol];
    od;
    return DD;
  else
    return CC;
  fi;
end;

PathMetric:=function(Graph, s)
  local n, VE, i, j;
  n:=Graph.order;
  VE:=[0];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(VE, Maximum(Distance(Graph, i, j), s));
    od;
  od;
  return VE;
end;

TwoValued:=function(Graph, a)
  local n, VE, i, j;
  n:=Graph.order;
  VE:=[0];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      if IsEdge(Graph, [i,j])=true then
	Add(VE, 1);
      else
	Add(VE, a);
      fi;
    od;
  od;
  return VE;
end;






#
#
# Group is assumed to be a permutation subgroup of Sym(n) leaving 
# the vector d invariant.
MembershipCutCone:=function(n,d,Group)
  local S, N, NullZ, ListSet, ListElement, ListV, input,A, outputCdd, iOrb, REDcutvectors, O, eElt, eList, LISTC, LIST, scalcut, iElt, H, DO, iDO, iCol, iDiff, Diff, Support, OldSupport, iC, ASS, Eo, Ecomb, idx, scal, VECT, p, Hyper, Comb;
  S:=[[1,1,-1],[1,1,1,-1,-1,0,0], [1,1,1,1,-1,-2], [2,1,1,-1,-1,-1], [1,1,1,1,-1,-1,-1], [2,2,1,-1,-1,-1,-1], [1,1,1,1,1,-2,-2], [2,1,1,1,-1,-1,-2], [3,1,1,-1,-1,-1,-1], [1,1,1,1,1,-1,-3]];
  N:=Length(d);
  NullZ:=ListWithIdenticalEntries(N, 0);
  ListV:=[];
  ListSet:=[];
  ListElement:=[];
  idx:=0;
  for Hyper in S
  do
    p:=Length(Hyper);
    O:=Orbit(SymmetricGroup(p), Hyper, Permuted);
    Comb:=Combinations([1..n],p);
    for Ecomb in Comb
    do
      for Eo in O
      do
	S:=ShallowCopy(NullZ);
	for iCol in [1..p]
	do
	  S[Ecomb[iCol]]:=Eo[iCol];
	od;
	VECT:=FromHypermetricVectorToHypermetricFace(S,"void");
	scal:=VECT*d;
	if scal<0 then
	  return false;
	fi;
	if scal=0 then
	  idx:=idx+1;
	  ListV[idx]:=S;
	  ListSet[idx]:=Ecomb;
	  ListElement[idx]:=Eo;
	fi;
      od;
    od;
  od;
  # build the cut system using the set of incidents
  ASS:=[];
  for iCol in [1..n]
  do
    ASS[iCol]:=-1;
  od;
  LIST:=[ASS];
  Support:=[];
  for iElt in [1..Length(ListSet)]
  do
    LISTC:=ShallowCopy(LIST);
    LIST:=ShallowCopy([]);
    # added elements
    OldSupport:=ShallowCopy(Support);
    Support:=Union(Support, ListSet[iElt]);
    Diff:=Difference(Support, OldSupport);
    DO:=BuildSet(Length(Diff),[0,1]);
    for iC in [1..Length(LISTC)]
    do
      for iDO in [1..Length(DO)]
      do
	H:=ShallowCopy(LISTC[iC]);
	for iDiff in [1..Length(Diff)]
	do
	  H[Diff[iDiff]]:=DO[iDO][iDiff];
	od;
	scalcut:=0;
	for iCol in [1..Length(ListElement[iElt])]
	do
	  if H[ListSet[iElt][iCol]]=1 then
	    scalcut:=scalcut+ListElement[iElt][iCol];
	  fi;
	od;
	if scalcut=0 or scalcut=1 then
	  Add(LIST, H);
	fi;
      od;
    od;
  od;
  # remove the cut whose first term is 1, this divides the size of cut set by 2
  LISTC:=ShallowCopy([]);
  for eList in LIST
  do
    if eList[1]=0 then
      Add(LISTC, eList);
    fi;
  od;
  # use the Group symmetry
  O:=Orbits(Group,LISTC, CutAction);
  NullZ:=ListWithIdenticalEntries(N+1, 0);
  REDcutvectors:=[];
  for iOrb in [1..Length(O)]
  do
    REDcutvectors[iOrb]:=NullZ;
    for eElt in O[iOrb]
    do
      REDcutvectors[iOrb]:=REDcutvectors[iOrb]+FromCutToCutVector(eElt,"extreme");
    od;
  od;
  outputCdd:=OutputTextFile("WORK/LP.ine", true);;
  AppendTo(outputCdd, "H-representation\n");
  AppendTo(outputCdd, "begin\n");
  WriteMatrix(outputCdd, REDcutvectors);
  AppendTo(outputCdd, "end\n");
  AppendTo(outputCdd, "minimize\n");
  AppendTo(outputCdd, " 0");
  WriteLine(outputCdd, d);
  CloseStream(outputCdd);
#  Exec("cddr+_gmp WORK/LP.ine > WORK/LP.stuff");
  Exec("cddr+_gmp WORK/LP.ine");
  Exec("./lpcddcleaner WORK/LP.lps > WORK/LP.gap");
  input:=InputTextFile("WORK/LP.gap");
  A:=ReadAll(input);
  CloseStream(input);
#  Exec("rm -f WORK/LP.lps WORK/LP.gap WORK/LP.stuff WORK/LP.ine");

  if A="optimum=0\n" then
    return "belong to CUT cone";
  else
    return "not belonging to CUT cone";
  fi;
end;


GRAPH_GetMultiComplement:=function(ListSize)
  local nbSize, n, GRA, idx, iSize, eSize, i, j, GRAcon;
  nbSize:=Length(ListSize);
  n:=Sum(ListSize);
  GRA:=NullGraph(Group(()), n);
  idx:=0;
  for iSize in [1..nbSize]
  do
    eSize:=ListSize[iSize];
    for i in [1..eSize-1]
    do
      for j in [i+1..eSize]
      do
        AddEdgeOrbit(GRA, [idx+i,idx+j]);
        AddEdgeOrbit(GRA, [idx+j,idx+i]);
      od;
    od;
    idx:=idx+eSize;
  od;
  GRAcon:=ComplementGraph(GRA);
  return GRAcon;
end;


CMC_CreateInformation:=function(ListReprFac, GRPperm, EXTref)
  local FAC, ListIncd, eRepr, Ofac, eIncd, eFAC, ListPermGens, eList, ePermFAC, GRPfac, eGen;
  FAC:=[];
  ListIncd:=[];
  for eRepr in ListReprFac
  do
    Ofac:=Orbit(GRPperm, eRepr, OnSets);
    for eIncd in Ofac
    do
      eFAC:=__FindFacetInequality(EXTref, eIncd);
      Add(ListIncd, eIncd);
      Add(FAC, eFAC);
    od;
  od;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRPperm)
  do
    eList:=List(ListIncd, x->Position(ListIncd, OnSets(x, eGen)));
    ePermFAC:=PermList(eList);
    Add(ListPermGens, ePermFAC);
  od;
  GRPfac:=Group(ListPermGens);
  return rec(EXT:=FAC, GRP:=GRPfac);
end;




CMC_EnumerateConnectedSimplicialComplex:=function(n, k)
  local ListSets, ListPermGen, eGen, eList, GRPperm, nbSet, ListOrbitFinal, IsCovering, IsEveryRidgeAtLeastTwice, IsCorrectExtension, GetListCand_Refined, GetListCand_All, FuncInsert, FuncInsertFinal, ListComplex, ListOrbit, NewListOrbit, iter, eFinal, fList, GetInvariantComplex;
  ListSets:=Combinations([1..n], k);
  ListPermGen:=[];
  for eGen in GeneratorsOfGroup(SymmetricGroup(n))
  do
    eList:=List(ListSets, x->Position(ListSets, OnSets(x, eGen)));
    Add(ListPermGen, PermList(eList));
  od;
  GRPperm:=Group(ListPermGen);
  nbSet:=Length(ListSets);
  ListOrbitFinal:=[];
  IsCovering:=function(eList)
    local eVect, eVal;
    eVect:=ListWithIdenticalEntries(n,0);
    for eVal in eList
    do
      eVect{ListSets[eVal]}:=ListWithIdenticalEntries(k,1);
    od;
    return Sum(eVect)=n;
  end;
  GetInvariantComplex:=function(eList)
    local ListRidge, ListNb, eVal, eSet, i, eDiff, eRidge, pos, ListFaceInv, singInv;
    ListRidge:=[];
    ListNb:=[];
    for eVal in eList
    do
      eSet:=ListSets[eVal];
      for i in [1..k]
      do
        eDiff:=Difference([1..k], [i]);
        eRidge:=eSet{eDiff};
        pos:=Position(ListRidge, eRidge);
        if pos=fail then
          Add(ListRidge, eRidge);
          Add(ListNb, 1);
        else
          ListNb[pos]:=ListNb[pos]+1;
        fi;
      od;
    od;
    ListFaceInv:=[];
    for eVal in eList
    do
      eSet:=ListSets[eVal];
      singInv:=[];
      for i in [1..k]
      do
        eDiff:=Difference([1..k], [i]);
        eRidge:=eSet{eDiff};
        pos:=Position(ListRidge, eRidge);
        Add(singInv, ListNb[pos]);
      od;
      Add(ListFaceInv, Collected(singInv));
    od;
    return Collected(ListFaceInv);
  end;
  IsEveryRidgeAtLeastTwice:=function(eList)
    local ListRidge, ListNb, eVal, eSet, i, eDiff, eRidge, pos;
    ListRidge:=[];
    ListNb:=[];
    for eVal in eList
    do
      eSet:=ListSets[eVal];
      for i in [1..k]
      do
        eDiff:=Difference([1..k], [i]);
        eRidge:=eSet{eDiff};
        pos:=Position(ListRidge, eRidge);
        if pos=fail then
          Add(ListRidge, eRidge);
          Add(ListNb, 1);
        else
          ListNb[pos]:=ListNb[pos]+1;
        fi;
      od;
    od;
    return Minimum(ListNb)>=2;
  end;
  FuncInsertFinal:=function(eList)
    local fList, test;
    if IsCovering(eList)=false then
      return;
    fi;
    if IsEveryRidgeAtLeastTwice(eList)=false then
      return;
    fi;
    for fList in ListOrbitFinal
    do
      test:=RepresentativeAction(GRPperm, eList, fList, OnSets);
      if test<>fail then
        return;
      fi;
    od;
    Add(ListOrbitFinal, eList);
  end;
  IsCorrectExtension:=function(eList, iSet)
    local eVal;
    for eVal in eList
    do
      if Length(Intersection(ListSets[eVal], ListSets[iSet]))=k-1 then
        return true;
      fi;
    od;
    return false;
  end;
  GetListCand_All:=function(eList)
    local TheListCand, iSet;
    TheListCand:=[];
    for iSet in [1..nbSet]
    do
      if Position(eList, iSet)=fail then
        if IsCorrectExtension(eList, iSet) then
          Add(TheListCand, Union(eList, [iSet]));
        fi;
      fi;
    od;
    return TheListCand;
  end;
  GetListCand_Refined:=function(eList)
    local ListRidge, ListNb, eVal, eSet, i, eDiff, eRidge, pos, ePartComplex, ListCand, eCand, iRidge;
    ListRidge:=[];
    ListNb:=[];
    for eVal in eList
    do
      eSet:=ListSets[eVal];
      for i in [1..k]
      do
        eDiff:=Difference([1..k], [i]);
        eRidge:=eSet{eDiff};
        pos:=Position(ListRidge, eRidge);
        if pos=fail then
          Add(ListRidge, eRidge);
          Add(ListNb, 1);
        else
          ListNb[pos]:=ListNb[pos]+1;
        fi;
      od;
    od;
    if Minimum(ListNb)>=2 then
      return GetListCand_All(eList);
    fi;
    ePartComplex:=ListSets{eList};
    ListCand:=[];
    for iRidge in [1..Length(ListRidge)]
    do
      if ListNb[iRidge]=1 then
        eRidge:=ListRidge[iRidge];
        for i in [1..n]
        do
          if Position(eRidge, i)=fail then
            eSet:=Union(eRidge, [i]);
	    pos:=Position(ListSets, eSet);
	    if Position(eList, pos)=fail then
	      eCand:=Union(eList, [pos]);
	      Add(ListCand, eCand);
	    fi;
          fi;
	od;
      fi;
    od;
#    Print("ePartComplex=", ePartComplex, " ListCand=", ListCand, "\n");
    return ListCand;
  end;
  ListOrbit:=[ [1] ];
  for iter in [2..nbSet-1]
  do
    NewListOrbit:=[];
    FuncInsert:=function(eOrb)
      local fRec, eInv, test;
      eInv:=GetInvariantComplex(eOrb);
      for fRec in NewListOrbit
      do
        if fRec.eInv=eInv then
          test:=RepresentativeAction(GRPperm, eOrb, fRec.eOrb, OnSets);
          if test<>fail then
            return;
          fi;
        fi;
      od;
      Add(NewListOrbit, rec(eOrb:=eOrb, eInv:=eInv));
    end;
    for eList in ListOrbit
    do
      for fList in GetListCand_Refined(eList)
      do
        FuncInsert(fList);
        FuncInsertFinal(fList);
      od;
    od;
    Print("iter=", iter, " / ", nbSet, " |ListOrbit|=", Length(ListOrbit), " |ListOrbitFinal|=", Length(ListOrbitFinal), "\n");
    ListOrbit:=List(NewListOrbit, x->x.eOrb);
  od;
  ListComplex:=[];
  for eFinal in ListOrbitFinal
  do
    Add(ListComplex, ListSets{eFinal});
  od;
  return ListComplex;
end;


#
# For k=1 we get the metric cone
#
CMC_GetCanonicalSimplicialInequality:=function(n,k)
  local ListSets, nbSet, ListIneq, eSubset, ListIdx, i, eDiff, iSet, eSet, pos, eIneq;
  ListSets:=Combinations([1..n], k+1);
  nbSet:=Length(ListSets);
  ListIneq:=[];
  for eSubset in Combinations([1..n], k+2)
  do
    ListIdx:=[];
    for i in [1..k+2]
    do
      eDiff:=Difference([1..k+2], [i]);
      eSet:=eSubset{eDiff};
      pos:=Position(ListSets, eSet);
      Add(ListIdx, pos);
    od;
    for i in [1..k+2]
    do
      eIneq:=ListWithIdenticalEntries(nbSet,0);
      eIneq{ListIdx}:=ListWithIdenticalEntries(k+2,1);
      eIneq[ListIdx[i]]:=-1;
      Add(ListIneq, eIneq);
    od;
  od;
  for iSet in [1..nbSet]
  do
    eIneq:=ListWithIdenticalEntries(nbSet,0);
    eIneq[iSet]:=1;
    Add(ListIneq, eIneq);
  od;
  return rec(ListSets:=ListSets, ListIneq:=ListIneq);
end;





CMC_GetCutPolytope:=function(TheGraph)
  local n, ListEdges, i, LAdj, j, eEdge, nbEdge, CUT_ext, ListSet, eSet, iEdge, eInt, eVect, fVect, ListPermGraph, eMat, eList, ePerm, eGen, nEdge, ePermEdge, eListB, eVectRed, fVectRed, GRPcanonic, ePermGraph, GRPvert, GRPedge, ListPermEdge, Overt, eO, fEdge, ListMatrGens, pos, ListPermGens, eMatrGen, CUT_info, MET_info, MET_info_symbolic, RecListOrbitCycle, RecOpt, ListRepresentativeFacetCut, FuncInsertOrbitFacetCut, eIneq, iAdj, iNextAdj, len, u, jEdge, eRepr, Oedge, eVert, ListSignedEdges, eSignEdge, fSignEdge, eSign, fSign, ListPermSignEdge, ePermSignEdge, GRPsignedEdge, HasCutInfo, ComputeCUTinformation, HasMetSymbolic, ComputeMETsymbolic, ListSymbolicRepresentativeFacet, GetMET_info, GetCUT_info, GetMET_info_symbolic, ComputeMET_info, GetMET_info_all, HasMetInfo, GetListSet;
  n:=TheGraph.order;
  ListEdges:=[];
  for i in [1..n-1]
  do
    LAdj:=Adjacency(TheGraph, i);
    for j in LAdj
    do
      if j>i then
        eEdge:=[i, j];
        Add(ListEdges, eEdge);
      fi;
    od;
  od;
  nbEdge:=Length(ListEdges);
  GRPvert:=AutGroupGraph(TheGraph);
  Overt:=Orbits(GRPvert, [1..n], OnPoints);
  ListMatrGens:=[];
  for eO in Overt
  do
    eVert:=eO[1];
    eMat:=NullMat(nbEdge+1,nbEdge+1);
    eMat[1][1]:=1;
    for iEdge in [1..nbEdge]
    do
      eEdge:=ListEdges[iEdge];
      if Position(eEdge, eVert)<>fail then
        eMat[1][iEdge+1]:=1;
        eMat[iEdge+1][iEdge+1]:=-1;
      else
        eMat[iEdge+1][iEdge+1]:=1;
      fi;
    od;
    Add(ListMatrGens, eMat);
  od;
  ListPermEdge:=[];
  for eGen in GeneratorsOfGroup(GRPvert)
  do
    eMat:=NullMat(1+nbEdge, 1+nbEdge);
    eMat[1][1]:=1;
    eList:=[];
    for iEdge in [1..nbEdge]
    do
      eEdge:=ListEdges[iEdge];
      fEdge:=OnSets(eEdge, eGen);
      pos:=Position(ListEdges, fEdge);
      eMat[1+iEdge][1+pos]:=1;
      Add(eList, pos);
    od;
    ePermEdge:=PermList(eList);
    Add(ListPermEdge, ePermEdge);
    Add(ListMatrGens, eMat);
  od;
  GRPedge:=Group(ListPermEdge);
  #
  # Now the edge symbolic computation
  #
  ListSignedEdges:=[];
  for iEdge in [1..nbEdge]
  do
    Add(ListSignedEdges, [iEdge, 1]);
    Add(ListSignedEdges, [iEdge, -1]);
  od;
  ListPermSignEdge:=[];
  for eGen in GeneratorsOfGroup(GRPvert)
  do
    eList:=[];
    for eSignEdge in ListSignedEdges
    do
      iEdge:=eSignEdge[1];
      eSign:=eSignEdge[2];
      eEdge:=ListEdges[iEdge];
      fEdge:=OnSets(eEdge, eGen);
      jEdge:=Position(ListEdges, fEdge);
      fSignEdge:=[jEdge, eSign];
      pos:=Position(ListSignedEdges, fSignEdge);
      Add(eList, pos);
    od;
    ePermSignEdge:=PermList(eList);
    if ePermSignEdge=fail then
      Error("Please debug from here");
    fi;
    Add(ListPermSignEdge, ePermSignEdge);
  od;
  for eO in Overt
  do
    eVert:=eO[1];
    eList:=[];
    for eSignEdge in ListSignedEdges
    do
      iEdge:=eSignEdge[1];
      eSign:=eSignEdge[2];
      eEdge:=ListEdges[iEdge];
      if Position(eEdge, eVert)<>fail then
        fSign:=-eSign;
      else
        fSign:= eSign;
      fi;
      fSignEdge:=[iEdge, fSign];
      pos:=Position(ListSignedEdges, fSignEdge);
      Add(eList, pos);
    od;
    ePermSignEdge:=PermList(eList);
    Add(ListPermSignEdge, ePermSignEdge);
  od;
  GRPsignedEdge:=Group(ListPermSignEdge);
  #
  # Now the CUT polytope
  #
  HasCutInfo:=false;
  ComputeCUTinformation:=function()
    if HasCutInfo then
      return;
    fi;
    HasCutInfo:=true;
    CUT_ext:=[];
    ListSet:=[];
    for eSet in Combinations([1..n-1])
    do
      Add(ListSet, eSet);
      eVect:=ListWithIdenticalEntries(nbEdge,0);
      for iEdge in [1..nbEdge]
      do
        eEdge:=ListEdges[iEdge];
        eInt:=Intersection(eEdge, eSet);
        if Length(eInt)=1 then
          eVect[iEdge]:=1;
        fi;
      od;
      fVect:=Concatenation([1], eVect);
      Add(CUT_ext, fVect);
    od;
    ListPermGens:=[];
    for eMatrGen in ListMatrGens
    do
      eList:=List(CUT_ext, x->Position(CUT_ext, x*eMatrGen));
      Add(ListPermGens, PermList(eList));
    od;
    GRPcanonic:=Group(ListPermGens);
    CUT_info:=rec(EXT:=CUT_ext, GRP:=GRPcanonic);
  end;
  GetCUT_info:=function()
    ComputeCUTinformation();
    return CUT_info;
  end;
  GetListSet:=function();
    ComputeCUTinformation();
    return ListSet;
  end;
  #
  # Now the MET symbolic info
  #
  HasMetSymbolic:=false;
  ComputeMETsymbolic:=function()
    local RecOpt, eRepr, len, i, iAdj, eIneqSymbolic, eIneqSymbolicIns, eEdge, iEdge, u, iNextAdj, fEdge, jEdge, Oedge, eO, fVert, TheInt, FuncInsertSymbolic, LocalList;
    if HasMetSymbolic then
      return;
    fi;
    HasMetSymbolic:=true;
    RecOpt:=rec(TheLen:=-1,
                UseMinimumOrbit:=true,
                RequireIrreducible:=true,
                RequireIsometricCycleFixedLength:=false,
                RequireIsometric:=false);
    RecListOrbitCycle:=GRAPH_EnumerateCycles(TheGraph, GRPvert, RecOpt);
    ListSymbolicRepresentativeFacet:=[];
    for eRepr in RecListOrbitCycle.FinalListOrb
    do
      LocalList:=[];
      FuncInsertSymbolic:=function(eSetSymb)
        local fSetSymb, test;
        for fSetSymb in LocalList
        do
          test:=RepresentativeAction(GRPsignedEdge, eSetSymb, fSetSymb, OnSets);
          if test<>fail then
            return;
          fi;
        od;
        Add(LocalList, eSetSymb);
      end;
      len:=Length(eRepr);
      for i in [1..len]
      do
        iAdj:=NextIdx(len, i);
        eIneqSymbolic:=[];
        eEdge:=Set([eRepr[i], eRepr[iAdj]]);
        iEdge:=Position(ListEdges, eEdge);
	Add(eIneqSymbolic, Position(ListSignedEdges, [iEdge, -1]));
        for u in [1..len-1]
        do
          iNextAdj:=NextIdx(len, iAdj);
          fEdge:=Set([eRepr[iNextAdj], eRepr[iAdj]]);
          jEdge:=Position(ListEdges, fEdge);
          Add(eIneqSymbolic, Position(ListSignedEdges, [jEdge, 1]));
          iAdj:=iNextAdj;
        od;
	eIneqSymbolicIns:=Set(eIneqSymbolic);
#        Print("i=", i, " eIneqSymbolicIns=", eIneqSymbolicIns, "\n");
	FuncInsertSymbolic(eIneqSymbolicIns);
      od;
#      Print("len=", len, " |LocalList|=", Length(LocalList), "\n");
      Append(ListSymbolicRepresentativeFacet, LocalList);
    od;
    Oedge:=Orbits(GRPedge, [1..nbEdge], OnPoints);
    for eO in Oedge
    do
      iEdge:=eO[1];
      eEdge:=ListEdges[iEdge];
      eVert:=eEdge[1];
      fVert:=eEdge[2];
      # The Inequalities x(e) >= 0 are needed only if the edge is not contained in a triangle
      TheInt:=Intersection(Adjacency(TheGraph, eVert), Adjacency(TheGraph, fVert));
      if Length(TheInt)=0 then
        eIneqSymbolic:=[Position(ListSignedEdges, [iEdge, 1])];
	Add(ListSymbolicRepresentativeFacet, eIneqSymbolic);
      fi;
    od;
  end;
  GetMET_info_symbolic:=function()
    local nbFac, eIneqSymbolic, eStab, OrbSiz;
    ComputeMETsymbolic();
    nbFac:=0;
    for eIneqSymbolic in ListSymbolicRepresentativeFacet
    do
      eStab:=Stabilizer(GRPsignedEdge, eIneqSymbolic, OnSets);
      OrbSiz:=Order(GRPsignedEdge) / Order(eStab);
      nbFac:=nbFac + OrbSiz;
    od;
    return [nbFac, Length(ListSymbolicRepresentativeFacet)];
  end;
  GetMET_info_all:=function()
    ComputeMETsymbolic();
    return rec(RecListOrbitCycle:=RecListOrbitCycle,
               ListSymbolicRepresentativeFacet:=ListSymbolicRepresentativeFacet,
               ListSignedEdges:=ListSignedEdges,
               GRPsignedEdge:=GRPsignedEdge);
  end;
  #
  # Now the MET info
  #
  HasMetInfo:=false;
  ComputeMET_info:=function()
    local ListRepresentativeFacetCut, FuncInsertFacet, eIneqSymbolic, eIneq, eVal, eSignEdge, iEdge, eSign;
    if HasMetInfo then
      return;
    fi;
    HasMetInfo:=true;
    ComputeMETsymbolic();
    ComputeCUTinformation();
    ListRepresentativeFacetCut:=[];
    FuncInsertFacet:=function(uIneq)
      local eSetIncd, i, eScal, fRepr, test;
      eSetIncd:=[];
      for i in [1..Length(CUT_ext)]
      do
        eScal:=CUT_ext[i]*eIneq;
        if eScal<0 then
          Error("eIneq is not a facet");
        fi;
        if eScal=0 then
          Add(eSetIncd, i);
        fi;
      od;
      if RankMat(CUT_ext{eSetIncd})<nbEdge then
        Print("eIneq=", eIneq, " is just a valid inequality (CUT)\n");
	return;
      fi;
      for fRepr in ListRepresentativeFacetCut
      do
        test:=RepresentativeAction(GRPcanonic, eSetIncd, fRepr, OnSets);
        if test<>fail then
          return;
        fi;
      od;
      Add(ListRepresentativeFacetCut, eSetIncd);
    end;
    for eIneqSymbolic in ListSymbolicRepresentativeFacet
    do
      eIneq:=ListWithIdenticalEntries(1+nbEdge, 0);
      for eVal in eIneqSymbolic
      do
        eSignEdge:=ListSignedEdges[eVal];
	iEdge:=eSignEdge[1];
	eSign:=eSignEdge[2];
	eIneq[1+iEdge]:=eSign;
      od;
      FuncInsertFacet(eIneq);
    od;
    Print("Before CMC_CreateInformation\n");
    MET_info:=CMC_CreateInformation(ListRepresentativeFacetCut, GRPcanonic, CUT_ext);
  end;
  GetMET_info:=function()
    ComputeMET_info();
    return MET_info;
  end;
  return rec(ListEdges:=ListEdges,
             GetCUT_info:=GetCUT_info,
             GetMET_info:=GetMET_info,
             GetMET_info_symbolic:=GetMET_info_symbolic,
             GetMET_info_all:=GetMET_info_all,
             GetListSet:=GetListSet, 
             GRPsignedEdge:=GRPsignedEdge,
             GRA:=TheGraph,
             GRPvert:=GRPvert,
             GRPedge:=GRPedge);
end;







BellPolytope_Attempt1:=function(TheGraph, ListWeight)
  local n, ListEdges, i, eAdj, eEdge, ListSeto, ListComb, EXT, eEXT, eV, i1, i2, eVal;
  n:=TheGraph.order;
  ListEdges:=[];
  for i in [1..n]
  do
    for eAdj in Adjacency(TheGraph, i)
    do
      if eAdj>i then
        eEdge:=[i,eAdj];
	Add(ListEdges, eEdge);
      fi;
    od;
  od;
  ListSeto:=[];
  for i in [1..n]
  do
    Add(ListSeto, [1..ListWeight[i]]);
  od;
  ListComb:=BuildSetMultiple(ListSeto);
  EXT:=[];
  for eV in ListComb
  do
    eEXT:=[1];
    for eEdge in ListEdges
    do
      i1:=eEdge[1];
      i2:=eEdge[2];
      if eV[i1]=eV[i2] then
        eVal:=1;
      else
        eVal:=0;
      fi;
      Add(eEXT, eVal);
    od;
    Add(EXT, eEXT);
  od;
  return rec(EXT:=EXT);

end;




#
#
#  Hypermetric Stuff,
#  Affine basis, Rank, SubGraphs, etc.
HypermetricCoordinates:=function(AffBas, Vertices)
  return List(Vertices, x->SolutionMat(AffBas, x));
end;



MatrixHypermetricInequalities:=function(ListHypCoord)
  return List(ListHypCoord, FromHypermetricVectorToHypermetricFace);
end;

#
#
# construction of complete distance system
DistanceConstructionDelaunay:=function(DistVector, Hcoord)
  local HypDim, DistMatrix, GramMatrix, NbV, DistMatrixExt, iVertex, jVertex, Vvector, Vred;
  HypDim:=Length(Hcoord[1]);
  DistMatrix:=DistanceVectorToDistanceMatrix(DistVector, HypDim);
  GramMatrix:=DistanceMatrixToGramMatrix(DistMatrix);
  NbV:=Length(Hcoord);
  DistMatrixExt:=NullMat(NbV, NbV);
  for iVertex in [1..NbV]
  do
    for jVertex in [1..NbV]
    do
      Vvector:=Hcoord[jVertex]-Hcoord[iVertex];
      Vred:=Vvector{[2..HypDim]};
      DistMatrixExt[iVertex][jVertex]:=Vred*GramMatrix*Vred;
    od;
  od;
  return DistMatrixExt;
end;



#
# Test whether d belongs to the hypermetric polytope
# that is whether for all b with
# (b1, ....., bn) s.t. sum b = 1 + 2*s
# we have
# sum_{i<j} b_i b_j d(i,j) <= s(s+1) = (S^2-1)/4
#
# Idea is following.
# ---The set of possible b is an affine set and it contains
#    (1,0, ..., 0)
# ---One basis can be obtained via
#    v1=(2, 0, ..., 0)
#    v2=(1, -1, 0, ..., 0)
#    .
#    .
#    vn=(0, ..., 0, 1, -1)
# ---Then we obtains a function to test whether a function of the form
#    A[x] + b[x] + c >= 0 for all x \in Z^n
# ---This is then done via the functionalities of
#    the Erdahl cone.
TestBelongingHypermetricPolytope:=function(eDist)
  local n, QuadMatA, QuadMatB, i, j, eAffBasis, eVect, TheReply, TheRec, eProd, eSol, b, ListB, ListDirB;
  n:=Length(eDist);
  # First the big matrix in terms of b
  QuadMatA:=NullMat(n+1,n+1);
  QuadMatA[1][1]:=-1/4;
  for i in [1..n]
  do
    for j in [1..n]
    do
      QuadMatA[i+1][j+1]:=QuadMatA[i+1][j+1] + 1/4;
    od;
  od;
  for i in [1..n]
  do
    for j in [1..n]
    do
      if i<>j then
        QuadMatA[i+1][j+1]:=QuadMatA[i+1][j+1] - eDist[i][j]/2;
      fi;
    od;
  od;
  eAffBasis:=[];
  Add(eAffBasis, Concatenation([1,1], ListWithIdenticalEntries(n-1,0)));
  Add(eAffBasis, Concatenation([0,2], ListWithIdenticalEntries(n-1,0)));
  for i in [1..n-1]
  do
    eVect:=ListWithIdenticalEntries(n+1,0);
    eVect[i+2]:=1;
    eVect[i+1]:=-1;
    Add(eAffBasis, eVect);
  od;
  QuadMatB:=eAffBasis*QuadMatA*TransposedMat(eAffBasis);
  TheReply:=InfDel_GetZeroSetKernel(QuadMatB);
  if IsBound(TheReply.error) then
    eSol:=TheReply.eVect;
    if Length(eSol)<>n+1 then
      Error("Wrong length in the vector");
    fi;
    eProd:=eSol*eAffBasis;
    b:=eProd{[2..n+1]};
    return rec(success:=false, b:=b);
  fi;
  TheRec:=TheReply.TheRec;
  #
  ListB:=[];
  for eVect in TheRec.EXT
  do
    eProd:=eVect*eAffBasis;
    b:=eProd{[2..n+1]};
    Add(ListB, b);
  od;
  ListDirB:=[];
  for eVect in TheRec.VectSpace
  do
    eProd:=eVect*eAffBasis;
    b:=eProd{[2..n+1]};
    Add(ListDirB, b);
  od;
  return rec(success:=true, ListB:=ListB, ListDirB:=ListDirB);
end;



FuncCanonicalizeHypIneq:=function(eIneq)
  local ePerm, eIneqB;
  ePerm:=SortingPerm(eIneq);
  eIneqB:=Permuted(eIneq, ePerm);
  return eIneqB;
end;

FuncCanonicalizeHypIneqSwitch:=function(eIneq)
  local fIneq, ePerm, eIneqB;
  fIneq:=List(eIneq, AbsInt);
  ePerm:=SortingPerm(fIneq);
  eIneqB:=Permuted(fIneq, ePerm);
  return eIneqB;
end;

GetHypermetricPolyAsVector:=function(eDist)
  local V, i, j, n;
  n:=Length(eDist);
  V:=[1];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(V, eDist[i][j]);
    od;
  od;
  return V;
end;


FuncCanonicalizePresent:=function(eIneq)
  local eIneqAbs, eMax, len, V, i, nbPlus, nbMinus;
  eIneqAbs:=List(eIneq, AbsInt);
  eMax:=Maximum(eIneqAbs);
  len:=Length(Filtered(eIneq, x->x=0));
  V:=[];
  Append(V, ListWithIdenticalEntries(len, 0));
  for i in [1..eMax]
  do
    nbPlus:=Length(Filtered(eIneq, x->x=i));
    nbMinus:=Length(Filtered(eIneq, x->x=-i));
    Append(V, ListWithIdenticalEntries(nbMinus, -i));
    Append(V, ListWithIdenticalEntries(nbPlus, i));
  od;
  return V;
end;




GenerateFullSwitchingFamily:=function(eIneq)
  local n, ListGen, eSet, fIneq, eVal, TheCan;
  n:=Length(eIneq);
  ListGen:=[];
  for eSet in Combinations([1..n])
  do
    fIneq:=ListWithIdenticalEntries(n,0);
    for eVal in eSet
    do
      fIneq[eVal]:=-eIneq[eVal];
    od;
    for eVal in Difference([1..n], eSet)
    do
      fIneq[eVal]:=eIneq[eVal];
    od;
    if Sum(fIneq)>0 then
      TheCan:=FuncCanonicalizeHypIneq(fIneq);
      Add(ListGen, TheCan);
    fi;
  od;
  return Set(ListGen);
end;


GetOrbitSizeHypermetricInequality:=function(eIneq)
  local n, eColl, eProd, OrbitSize;
  n:=Length(eIneq)-1;
  eColl:=Collected(eIneq);
  eProd:=Product(List(eColl, x->Factorial(x[2])));
  OrbitSize:=Factorial(n+1)/eProd;
  return OrbitSize;
end;

GetOrbitInequalityHypermetricCone:=function(n)
  local eDir, eFile, k, TheRet, eVect, eRed, eVectRed;
  if n>9 then
    Error("Results are not known beyond dimension 9");
  fi;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/HypermetricIneq")[1];
  eFile:=Filename(eDir, "HypermetricIneq8");
  k:=8 - n;
  TheRet:=[];
  for eVect in ReadAsFunction(eFile)()
  do
    eRed:=eVect{[1..k]};
    if eRed=ListWithIdenticalEntries(k, 0) then
      eVectRed:=eVect{[k+1..8]};
      Add(TheRet, eVectRed);
    fi;
  od;
  return TheRet;
end;

GetFullCutRecord:=function(n)
  local ListAllCut, ListAllVect, eSet, eDist, eVect, i, j, eEdge, eInt, eVal;
  ListAllCut:=[];
  ListAllVect:=[];
  for eSet in Combinations([1..n-1])
  do
    eDist:=NullMat(n,n);
    eVect:=[1];
    for i in [1..n-1]
    do
      for j in [i+1..n]
      do
        eEdge:=Set([i,j]);
        eInt:=Intersection(eEdge, eSet);
        if Length(eInt)=1 then
          eVal:=1;
        else
          eVal:=0;
        fi;
        Add(eVect, eVal);
        eDist[i][j]:=eVal;
        eDist[j][i]:=eVal;
      od;
    od;
    Add(ListAllCut, eDist);
    Add(ListAllVect, eVect);
  od;
  return rec(ListAllCut:=ListAllCut,
             ListAllVect:=ListAllVect);
end;



GetDistMatrixAsVector:=function(eDist)
  local n, V, i, j;
  n:=Length(eDist);
  V:=[];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(V, eDist[i][j]);
    od;
  od;
  return V;
end;

GetVectorFromHypermetric:=function(eIneq)
  local n, V, i, j;
  n:=Length(eIneq);
  V:=[];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(V, eIneq[i]*eIneq[j]);
    od;
  od;
  return V;
end;

GetHypermetricPolytopeInequality:=function(eIneq)
  local eSum, s, eCst;
  eSum:=Sum(eIneq);
  s:=(eSum-1)/2;
  eCst:=s*(s+1);
  return Concatenation([eCst], -GetVectorFromHypermetric(eIneq));
end;


GetPolytopeHypermetricInequality:=function(eIneq)
  local eSum, s, eCst, V, i, j, n;
  n:=Length(eIneq);
  eSum:=Sum(eIneq);
  s:=(eSum-1)/2;
  if IsInt(s)=false then
    Error("s should be integral");
  fi;
  eCst:=s*(s+1);
  V:=[eCst];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(V, -eIneq[i]*eIneq[j]);
    od;
  od;
  return V;
end;



GetRecIsomorphismHypermetricPolytopeEXT:=function(n)
  local eSym, ListV, V1, V2, FAC, GRP, eList, ePerm, ListPermGens, eGen, GRPsymmetric, GetOrbitStabSize, GetInvariantHypermetricPoly, TestEquivalenceHypermetricPoly, NumberOrbitSplitting, StabilizerHypermetricPoly, GetStabOrbitSize;
  eSym:=SymmetricGroup(n);
  ListV:=[];
  V1:=Concatenation([-1,1,1],ListWithIdenticalEntries(n-3,0));
  Append(ListV, Orbit(eSym, V1, Permuted));
  V2:=Concatenation([1,1,1] ,ListWithIdenticalEntries(n-3,0));
  Append(ListV, Orbit(eSym, V2, Permuted));
  FAC:=List(ListV, GetPolytopeHypermetricInequality);
  GRP:=LinPolytope_Automorphism(FAC);
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(eSym)
  do
    eList:=List(ListV, x->Position(ListV, Permuted(x, eGen)));
    ePerm:=PermList(eList);
    Add(ListPermGens, ePerm);
  od;
  GRPsymmetric:=Group(ListPermGens);
  TotalGroup:=2^(n-1)*Factorial(n);
  GetInvariantHypermetricPoly:=function(eDist)
    local eVert;
    eVert:=GetHypermetricPolyAsVector(eDist);
    return Collected(FAC*eVert);
  end;
  TestEquivalenceHypermetricPoly:=function(eDist1, eDist2)
    local eVert1, eVert2, ListScal1, ListScal2, test;
    eVert1:=GetHypermetricPolyAsVector(eDist1);
    eVert2:=GetHypermetricPolyAsVector(eDist2);
    ListScal1:=FAC*eVert1;
    ListScal2:=FAC*eVert2;
    test:=PermutedRepresentativeAction(GRP, ListScal1, ListScal2);
    if test=fail then
      return false;
    fi;
    return true;
  end;
  NumberOrbitSplitting:=function(eDistPoly)
    local eVert, ListScal, eStab, LDCS;
    eVert:=GetHypermetricPolyAsVector(eDistPoly);
    ListScal:=FAC*eVert;
    eStab:=PermutedStabilizer(GRP, ListScal);
    LDCS:=DoubleCosets(GRP, eStab, GRPsymmetric);
    return Length(LDCS);
  end;
  StabilizerHypermetricPoly:=function(eDist, FACselection)
    local eVert, ListScal, eStab, ListPermGens, eGen, eMatr, eList, ePerm, eStabFACselection;
    eVert:=GetHypermetricPolyAsVector(eDist);
    ListScal:=FAC*eVert;
    eStab:=PermutedStabilizer(GRP, ListScal);
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(eStab)
    do
      eMatr:=FindTransformation(FAC, FAC, eGen);
      eList:=List(FACselection, x->Position(FACselection, x*eMatr));
      if Position(eList, fail)<>fail then
        Error("The vertex is not invariant");
      fi;
      ePerm:=PermList(eList);
      Add(ListPermGens, ePerm);
    od;
    eStabFACselection:=PersoGroupPerm(ListPermGens);
    return rec(eStabMET:=eStab, 
               eStabFACselection:=eStabFACselection);
  end;
  GetStabOrbitSize:=function(eDist)
    local eVert, ListScal, eStab, eOrbitSize;
    eVert:=GetHypermetricPolyAsVector(eDist);
    ListScal:=FAC*eVert;
    eStab:=PermutedStabilizer(GRP, ListScal);
    eOrbitSize:=TotalGroup/Order(eStab);
    return rec(eStab:=eStab, eOrbitSize:=eOrbitSize);
  end;
  return rec(n:=n, 
             ListV:=ListV, 
             FAC:=FAC, 
             GRP:=GRP, 
             GRPsymmetric:=GRPsymmetric, 
             GetInvariantHypermetricPoly:=GetInvariantHypermetricPoly, 
             TestEquivalenceHypermetricPoly:=TestEquivalenceHypermetricPoly,
             NumberOrbitSplitting:=NumberOrbitSplitting, 
             StabilizerHypermetricPoly:=StabilizerHypermetricPoly,
             GetStabOrbitSize:=GetStabOrbitSize);
end;


GetRecIsomorphismHypermetricPolytopeFAC:=function(n)
  local ListEdges, i, j, EXT, ListSets, eSet, eVet, eEdge, eInt, eVect, GRP, eVal, StabilizerHypermetricPolyFacet, GetOrbitSizeFacetHypermetricPolytope, TotalGroupSize;
  ListEdges:=[];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      eEdge:=Set([i,j]);
      Add(ListEdges, eEdge);
    od;
  od;
  EXT:=[];
  ListSets:=Combinations([1..n-1]);
  for eSet in ListSets
  do
    eVect:=[1];
    for eEdge in ListEdges
    do
      eInt:=Intersection(eEdge, eSet);
      if Length(eInt)=1 then
        eVal:=1;
      else
        eVal:=0;
      fi;
      Add(eVect, eVal);
    od;
    Add(EXT, eVect);
  od;
  GRP:=LinPolytope_Automorphism(EXT);
  TotalGroupSize:=2^(n-1)*Factorial(n);
  StabilizerHypermetricPolyFacet:=function(eFAC)
    local ListScal, eStab;
    ListScal:=EXT*eFAC;
    eStab:=PermutedStabilizer(GRP, ListScal);
    return rec(eStabCUT:=eStab);
  end;
  GetOrbitSizeFacetHypermetricPolytope:=function(eIneq)
    local RecStab, eOrbSize, eFAC;
    eFAC:=GetHypermetricPolytopeInequality(eIneq);
    RecStab:=StabilizerHypermetricPolyFacet(eFAC);
    eOrbSize:=TotalGroupSize/Order(RecStab.eStabCUT);
    return eOrbSize;
  end;
  return rec(ListSets:=ListSets, 
             EXT:=EXT, 
             GRP:=GRP,
             StabilizerHypermetricPolyFacet:=StabilizerHypermetricPolyFacet, 
             GetOrbitSizeFacetHypermetricPolytope:=GetOrbitSizeFacetHypermetricPolytope);
end;

GetOrientedMulticut:=function(eRec, ListSets)
  local n, eVect, nbSet, iSet, eSet, V, eC, i, j, eVal;
  n:=eRec.n;
  eVect:=ListWithIdenticalEntries(n,0);
  nbSet:=Length(ListSets);
  for iSet in [1..nbSet]
  do
    eSet:=ListSets[iSet];
    eVect{eSet}:=ListWithIdenticalEntries(Length(eSet),iSet);
  od;
  V:=[1];
  for eC in eRec.ListC
  do
    i:=eC[1];
    j:=eC[2];
    if eVect[i]<eVect[j] then
      eVal:=1;
    else
      eVal:=0;
    fi;
    Add(V, eVal);
  od;
  return V;
end;





Cone_OCUT:=function(n)
  local LSET, EXT, eSet, V, i, j, H, DistMat, eList, GRP, LSymb, ListC;
  LSET:=Combinations([1..n]);
  #
  EXT:=[];
  ListC:=[];
  for i in [1..n]
  do
    for j in [1..n]
    do
      if i<>j then
        Add(ListC, [i,j]);
      fi;
    od;
  od;
  for eSet in LSET
  do
    V:=[];
    if Length(eSet)<>0 and Length(eSet)<>n then
      for i in [1..n]
      do
        for j in [1..n]
        do
          if i<>j then
            if Position(eSet, i)=fail and Position(eSet, j)<>fail then
              Add(V, 1);
            else
              Add(V, 0);
            fi;
          fi;
        od;
      od;
      Add(EXT, V);
    fi;
  od;
  return rec(EXT:=EXT, ListC:=ListC, n:=n);
end;


PolyB_OCUT:=function(n)
  local LSET, EXT, eSet, V, i, j, H, DistMat, eList, GRP, LSymb, ListC;
  LSET:=Combinations([1..n]);
  #
  EXT:=[];
  ListC:=[];
  for i in [1..n]
  do
    for j in [1..n]
    do
      if i<>j then
        Add(ListC, [i,j]);
      fi;
    od;
  od;
  LSymb:=[];
  for eSet in LSET
  do
    if Length(eSet)<>n then
      Add(LSymb, eSet);
      V:=[1];
      for i in [1..n]
      do
        for j in [1..n]
        do
          if i<>j then
            if Position(eSet, i)=fail and Position(eSet, j)<>fail then
              Add(V, 1);
            else
              Add(V, 0);
            fi;
          fi;
        od;
      od;
      Add(EXT, V);
    fi;
  od;
  return rec(EXT:=EXT, LSymb:=LSymb, ListC:=ListC, n:=n);
end;

Poly_QMET:=function(n)
  local LSET, EXT, eSet, V, i, j, k, H, DistMat, eList, GRP, LSymb, ListC, pos1, pos2, pos3, pos1b, pos2b, pos3b, fSet, NSP, FAC, FAChom, nbC, ePerm, ListEqua, eFac, PreFAChom, eMat, ListMatrGens, eC1, eC2, iC, eCP, eC, pos, GRPmatr, eGen, eColl, iP, jP, eEnt, LSymbIneq, eSymb, IsFirst1, IsFirst2, ListRepresentatives, ListSwitchingMatrices, iSwitch, ListIndexes, ListNatureIneq, eDiff, GRPsymrev;
  #
  ListC:=[];
  for i in [1..n]
  do
    for j in [1..n]
    do
      if i<>j then
        Add(ListC, [i,j]);
      fi;
    od;
  od;
  nbC:=Length(ListC);
  LSymb:=[];
  FAC:=[];
  LSymbIneq:=[];
  IsFirst1:=true;
  IsFirst2:=true;
  ListRepresentatives:=[];
  ListNatureIneq:=[];
  for eSet in Combinations([1..n],3)
  do
    for ePerm in SymmetricGroup(3)
    do
      fSet:=Permuted(eSet, ePerm);
      i:=fSet[1];
      j:=fSet[2];
      k:=fSet[3];
      V:=[0];
      Append(V, ListWithIdenticalEntries(nbC,0));
      pos1:=Position(ListC, [i,j]);
      pos2:=Position(ListC, [i,k]);
      pos3:=Position(ListC, [k,j]);
      V[pos1+1]:=-1;
      V[pos2+1]:=1;
      V[pos3+1]:=1;
      eSymb:=Concatenation("OT(", String(i), String(j), ",", String(k), ")");
      Add(FAC, V);
      Add(ListNatureIneq, 0);
      Add(LSymbIneq, eSymb);
      if IsFirst1=true then
        Add(ListRepresentatives, Length(FAC));
      fi;
      IsFirst1:=false;
    od;
    for ePerm in SymmetricGroup(2)
    do
      fSet:=Permuted(eSet, ePerm);
      V:=[2];
      i:=fSet[1];
      j:=fSet[2];
      k:=fSet[3];
      Append(V, ListWithIdenticalEntries(nbC,0));
      pos1:=Position(ListC, [i,j]);
      pos2:=Position(ListC, [j,k]);
      pos3:=Position(ListC, [k,i]);
      V[pos1+1]:=-1;
      V[pos2+1]:=-1;
      V[pos3+1]:=-1;
      eSymb:=Concatenation("C(", String(i), String(j), String(k), ")");
      Add(FAC, V);
      Add(ListNatureIneq, 1);
      Add(LSymbIneq, eSymb);
      if IsFirst2=true then
        Add(ListRepresentatives, Length(FAC));
      fi;
      IsFirst2:=false;
    od;
  od;
  IsFirst1:=true;
  for iC in [1..nbC]
  do
    eC:=ListC[iC];
    i:=eC[1];
    j:=eC[2];
    V:=[0];
    Append(V, ListWithIdenticalEntries(nbC,0));
    V[iC+1]:=1;
    eSymb:=Concatenation("NN(", String(i), String(j), ")");
    Add(FAC, V);
    Add(ListNatureIneq, 0);
    Add(LSymbIneq, eSymb);
    if IsFirst1=true then
      Add(ListRepresentatives, Length(FAC));
    fi;
    V:=[1];
    Append(V, ListWithIdenticalEntries(nbC,0));
    V[iC+1]:=-1;
    eSymb:=Concatenation("NM(", String(i), String(j), ")");
    Add(FAC, V);
    Add(ListNatureIneq, 1);
    Add(LSymbIneq, eSymb);
    if IsFirst1=true then
      Add(ListRepresentatives, Length(FAC));
    fi;
    IsFirst1:=false;
  od;
  ListEqua:=[];
  for eSet in Combinations([1..n],3)
  do
    i:=eSet[1];
    j:=eSet[2];
    k:=eSet[3];
    pos1:=Position(ListC, [i,j]);
    pos1b:=Position(ListC, [j,i]);
    pos2:=Position(ListC, [j,k]);
    pos2b:=Position(ListC, [k,j]);
    pos3:=Position(ListC, [k,i]);
    pos3b:=Position(ListC, [i,k]);
    V:=[0];
    Append(V, ListWithIdenticalEntries(nbC,0));
    V[pos1+1]:=1;
    V[pos2+1]:=1;
    V[pos3+1]:=1;
    V[pos1b+1]:=-1;
    V[pos2b+1]:=-1;
    V[pos3b+1]:=-1;
    Add(ListEqua, V);
  od;
  NSP:=NullspaceMat(TransposedMat(ListEqua));
  PreFAChom:=[];
  for eFac in FAC
  do
    eList:=List(NSP, x->x*eFac);
    Add(PreFAChom, eList);
  od;
  eColl:=Collected(PreFAChom);
  for eEnt in eColl
  do
#    Print(" ", eEnt[2]);
    if eEnt[2]=2 then
#      Print("doubled is ", eEnt[1], "\n");
    fi;
  od;
  Print("\n");
  FAChom:=Set(PreFAChom);
  ListIndexes:=List(FAChom, x->Position(PreFAChom, x));
#  Print("|PreFAChom|=", Length(PreFAChom), " |FAChom|=", Length(FAChom), "\n");
  #
  ListMatrGens:=[];
  for eGen in GeneratorsOfGroup(SymmetricGroup(n))
  do
    eMat:=NullMat(nbC+1,nbC+1);
    eMat[1][1]:=1;
    for iC in [1..nbC]
    do
      eC:=ListC[iC];
      i:=eC[1];
      j:=eC[2];
      iP:=OnPoints(i, eGen);
      jP:=OnPoints(j, eGen);
      eCP:=[iP, jP];
      pos:=Position(ListC, eCP);
      eMat[iC+1][pos+1]:=1;
    od;
    Add(ListMatrGens, eMat);
  od;
  #
  eMat:=NullMat(nbC+1,nbC+1);
  eMat[1][1]:=1;
  for iC in [1..nbC]
  do
    eC:=ListC[iC];
    eCP:=Reversed(eC);
    pos:=Position(ListC, eCP);
    eMat[iC+1][pos+1]:=1;
  od;
  Add(ListMatrGens, eMat);
  GRPsymrev:=Group(ListMatrGens);
  #
  ListSwitchingMatrices:=[];
  for iSwitch in [1..n]
  do
    eMat:=NullMat(nbC+1,nbC+1);
    eMat[1][1]:=1;
    eDiff:=Difference([1..n], [iSwitch]);
    for i in eDiff
    do
      for j in eDiff
      do
        if i<>j then
          pos:=Position(ListC, [i,j]);
          eMat[pos+1][pos+1]:=1;
        fi;
      od;
    od;
    for i in eDiff
    do
      eC1:=[iSwitch,i];
      eC2:=[i,iSwitch];
      pos1:=Position(ListC, eC1);
      pos2:=Position(ListC, eC2);
      eMat[pos1+1][pos2+1]:=-1;
      eMat[pos2+1][pos1+1]:=-1;
      eMat[1][pos1+1]:=1;
      eMat[1][pos2+1]:=1;
    od;
    Add(ListSwitchingMatrices, eMat);
  od;
  Add(ListMatrGens, ListSwitchingMatrices[1]);
  GRPmatr:=Group(ListMatrGens);
  #
  return rec(n:=n,
             FAC:=FAC,
             ListIndexes:=ListIndexes,
             ListNatureIneq:=ListNatureIneq,
             LSymbIneq:=LSymbIneq,
             GRPmatr:=GRPmatr,
             FAChom:=FAChom,
             NSP:=NSP,
             ListEqua:=ListEqua,
             LSymb:=LSymb,
             ListC:=ListC,
             ListRepresentatives:=ListRepresentatives,
             GRPsymrev:=GRPsymrev);
end;

Cone_GetWeightedPresentation:=function(eRec, eEXT)
  local n, eReducedEXT, i, j, pos, eWeight, pos1, pos2;
  n:=eRec.n;
  eReducedEXT:=[];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      pos:=Position(eRec.ListC, [i,j]);
      Add(eReducedEXT, eEXT[pos]);
    od;
  od;
  for i in [2..n]
  do
    pos1:=Position(eRec.ListC, [1,i]);
    pos2:=Position(eRec.ListC, [i,1]);
    eWeight:=eEXT[pos1]-eEXT[pos2];
    Add(eReducedEXT, eWeight);
  od;
  return eReducedEXT;
end;

Poly_GetWeightedPresentation:=function(eRec, eEXT)
  local n, eReducedEXT, i, j, pos, eWeight, pos1, pos2;
  n:=eRec.n;
  eReducedEXT:=[1];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      pos:=Position(eRec.ListC, [i,j]);
      Add(eReducedEXT, eEXT[pos+1]);
    od;
  od;
  for i in [2..n]
  do
    pos1:=Position(eRec.ListC, [1,i]);
    pos2:=Position(eRec.ListC, [i,1]);
    eWeight:=eEXT[pos1+1]-eEXT[pos2+1];
    Add(eReducedEXT, eWeight);
  od;
  return eReducedEXT;
end;



Poly_OCUT:=function(n)
  local eRec, GRPmatr, nbLow, EXT, i, eSet1, eSet2, ListSets, eRay, O, EXTproj, ListPermGens, eGen, GRPperm, ListMat, eMat, GRPmatrRes, eIndexLow, GRPmatrResCongr, ListMatCongr, eIndexHigh, eSetWeight, eList;
  eRec:=Poly_QMET(n);
  GRPmatr:=eRec.GRPmatr;
  nbLow:=LowerInteger(n/2);
  EXT:=[];
  for i in [0..nbLow]
  do
    eSet1:=[1..i];
    eSet2:=[i+1..n];
    ListSets:=[eSet1, eSet2];
    eRay:=GetOrientedMulticut(eRec, ListSets);
    O:=Orbit(GRPmatr, eRay, OnPoints);
    Print("ListSets=", ListSets, " |O|=", Length(O), "\n");
    Append(EXT, O);
  od;
  EXTproj:=List(EXT, x->Poly_GetWeightedPresentation(eRec, x));
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRPmatr)
  do
    eList:=List(EXT, x->Position(EXT, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  GRPperm:=Group(ListPermGens);
  ListMat:=[];
  ListMatCongr:=[];
  for eGen in ListPermGens
  do
    eMat:=FindTransformation(EXTproj, EXTproj, eGen);
    Add(ListMat, eMat);
    Add(ListMatCongr, TransposedMat(eMat));
  od;
  GRPmatrRes:=Group(ListMat);
  GRPmatrResCongr:=Group(ListMatCongr);
  eIndexLow:=1+n*(n-1)/2+1;
  eIndexHigh:=Length(EXTproj[1]);
  eSetWeight:=[eIndexLow..eIndexHigh];
  return rec(n:=n, EXT:=EXT, GRPperm:=GRPperm, EXTproj:=EXTproj, GRPmatrRes:=GRPmatrRes, GRPmatrResCongr:=GRPmatrResCongr, GRPmatr:=GRPmatr, ListC:=eRec.ListC, eSetWeight:=eSetWeight);
end;

Poly_OMCUT:=function(n)
  local eRec, GRPmatr, EXT, ePartition, eRay, O, rnkFac, rnkExt, GRP, eFac, test, ListPermGens, eList, eMatr;
  eRec:=Poly_QMET(n);
  GRPmatr:=eRec.GRPmatr;
  EXT:=[];
  for ePartition in GenerationRamanujanPartitions(n)
  do
    eRay:=GetOrientedMulticut(eRec, ePartition);
    O:=Orbit(GRPmatr, eRay, OnPoints);
    Append(EXT, O);
  od;
  rnkFac:=RankMat(eRec.FAC);
  rnkExt:=RankMat(EXT);
  Print("rnkFac=", rnkFac, " rnkExt=", rnkExt, " |EXT|=", Length(EXT), "\n");
  for eFac in eRec.FAC
  do
    test:=First(EXT, x->EXT*eFac<0);
    if test<>fail then
      Error("Some points are not in QMETP_n");
    fi;
  od;
  ListPermGens:=[];
  for eMatr in GeneratorsOfGroup(GRPmatr)
  do
    eList:=List(EXT, x->Position(EXT, x*eMatr));
    Add(ListPermGens, PermList(eList));
  od;
  GRP:=Group(ListPermGens);
  return rec(n:=n,
             EXT:=EXT,
             FAC_qmet:=eRec.FAC,
             GRPperm:=GRP);
end;




Cone_QMET:=function(n)
  local LSET, EXT, eSet, V, i, j, k, H, DistMat, eList, GRP, LSymb, ListC, pos1, pos2, pos3, pos1b, pos2b, pos3b, fSet, NSP, FAC, FAChom, nbC, ePerm, ListEqua, eFac, PreFAChom, eMat, ListMatrGens, eC1, eC2, iC, eCP, eC, pos, GRPmatr, eGen, eColl, iP, jP, eEnt;
  #
  ListC:=[];
  for i in [1..n]
  do
    for j in [1..n]
    do
      if i<>j then
        Add(ListC, [i,j]);
      fi;
    od;
  od;
  nbC:=Length(ListC);
  LSymb:=[];
  FAC:=[];
  for eSet in Combinations([1..n],3)
  do
    for ePerm in SymmetricGroup(3)
    do
      fSet:=Permuted(eSet, ePerm);
      i:=fSet[1];
      j:=fSet[2];
      k:=fSet[3];
      V:=[0];
      Append(V, ListWithIdenticalEntries(nbC,0));
      pos1:=Position(ListC, [i,j]);
      pos2:=Position(ListC, [i,k]);
      pos3:=Position(ListC, [k,j]);
      V[pos1+1]:=-1;
      V[pos2+1]:=1;
      V[pos3+1]:=1;
      Add(FAC, V);
    od;
  od;
  for i in [1..nbC]
  do
    V:=[0];
    Append(V, ListWithIdenticalEntries(nbC,0));
    V[i+1]:=1;
    Add(FAC, V);
  od;
  ListEqua:=[];
  for eSet in Combinations([1..n],3)
  do
    i:=eSet[1];
    j:=eSet[2];
    k:=eSet[3];
    pos1:=Position(ListC, [i,j]);
    pos1b:=Position(ListC, [j,i]);
    pos2:=Position(ListC, [j,k]);
    pos2b:=Position(ListC, [k,j]);
    pos3:=Position(ListC, [k,i]);
    pos3b:=Position(ListC, [i,k]);
    V:=[0];
    Append(V, ListWithIdenticalEntries(nbC,0));
    V[pos1+1]:=1;
    V[pos2+1]:=1;
    V[pos3+1]:=1;
    V[pos1b+1]:=-1;
    V[pos2b+1]:=-1;
    V[pos3b+1]:=-1;
    Add(ListEqua, V);
  od;
  NSP:=NullspaceMat(TransposedMat(ListEqua));
  PreFAChom:=[];
  for eFac in FAC
  do
    eList:=List(NSP, x->x*eFac);
    Add(PreFAChom, eList);
  od;
  eColl:=Collected(PreFAChom);
  for eEnt in eColl
  do
    Print(" ", eEnt[2]);
  od;
  Print("\n");
  FAChom:=Set(PreFAChom);
  Print("|PreFAChom|=", Length(PreFAChom), " |FAChom|=", Length(FAChom), "\n");
  #
  ListMatrGens:=[];
  for eGen in GeneratorsOfGroup(SymmetricGroup(n))
  do
    eMat:=NullMat(nbC+1,nbC+1);
    eMat[1][1]:=1;
    for iC in [1..nbC]
    do
      eC:=ListC[iC];
      i:=eC[1];
      j:=eC[2];
      iP:=OnPoints(i, eGen);
      jP:=OnPoints(j, eGen);
      eCP:=[iP, jP];
      pos:=Position(ListC, eCP);
      eMat[iC+1][pos+1]:=1;
    od;
    Add(ListMatrGens, eMat);
  od;
  #
  eMat:=NullMat(nbC+1,nbC+1);
  eMat[1][1]:=1;
  for iC in [1..nbC]
  do
    eC:=ListC[iC];
    eCP:=Reversed(eC);
    pos:=Position(ListC, eCP);
    eMat[iC+1][pos+1]:=1;
  od;
  Add(ListMatrGens, eMat);
  GRPmatr:=Group(ListMatrGens);
  #
  return rec(FAC:=FAC, GRPmatr:=GRPmatr, FAChom:=FAChom, NSP:=NSP, ListEqua:=ListEqua, LSymb:=LSymb, ListC:=ListC, n:=n);
end;




GetPermutationGroupFromMatrixGroup:=function(EXTin, GRPmatrIn)
  local ListPermGens, eMatrGen, eList;
  ListPermGens:=[];
  for eMatrGen in GeneratorsOfGroup(GRPmatrIn)
  do
    eList:=List(EXTin, x->Position(EXTin, x*eMatrGen));
    Add(ListPermGens, PermList(eList));
  od;
  return Group(ListPermGens);
end;

PrintKeyData_info:=function(string, eInfo)
  local Opt;
  Opt:=Orbits(eInfo.GRP, [1..Length(eInfo.EXT)], OnPoints);
  Print("polytope ", string, " |EXT|=", Length(eInfo.EXT), " rank(EXT)=", PersoRankMat(eInfo.EXT), " |GRP|=", Order(eInfo.GRP), " |Opt|=", Length(Opt), "\n");
end;


CMC_GetCutPolytopeOriented:=function(TheGraph)
  local n, ListOrientedEdges, ListListAdj, i, j, LAdj, nbOrEdge, GRPvert, ListMatrGens, ListPermOrEdge, eGen, TheMat, eListOrEdge, iOrEdge, eOrEdge, fOrEdge, pos, eDiff, ePermOrEdge, pos1, pos2, eC1, eC2, GRPoredge, GRPmatr, iSwitch, nbLow, eSet1, eSet2, CUTocut_exthigh, CUTomcut_ext, eRay, O, GetOrientedMulticutGraph, ePartition, CUTocut_grpext, CUTomcut_grpext, eScal, ListSets, rankOmcut, RecListOrbitCycle, ListRepresentativeFacetOmcut, SubsequentIdx, eIneq, iNextAdj, iAdj, METomcut_fac, METomcut_repr, ePermMETomcut, ListPermGensMETomcut, METomcut_grpfac, RecOpt, FuncInsertOrbitFacetOmcut, eChoice, len, u, Ooredge, eO, Ofac, jOrEdge, kOrEdge, gOrEdge, eInt, eReprFac, eFAC, eList, eRepr, eSelect, FuncInsertOrbitFacetOcut, ListRepresentativeFacetRaw, METomcut_info, METocut_info, ListRepresentativeFacetOcut, CUTocut_ext, CUTocut_info, CUTomcut_info, Overt, iVert, GetOMCUT_met, GetOMCUT_cut, OmcutComputed, ComputeOmcutRelated;
  n:=TheGraph.order;
  ListOrientedEdges:=[];
  ListListAdj:=[];
  for i in [1..n]
  do
    LAdj:=Adjacency(TheGraph, i);
    Add(ListListAdj, LAdj);
    for j in LAdj
    do
      eOrEdge:=[i, j];
      Add(ListOrientedEdges, eOrEdge);
    od;
  od;
  nbOrEdge:=Length(ListOrientedEdges);
  #
  # The matrix generators, first from graph symmetries
  #
  GRPvert:=AutGroupGraph(TheGraph);
  ListMatrGens:=[];
  ListPermOrEdge:=[];
  for eGen in GeneratorsOfGroup(GRPvert)
  do
    TheMat:=NullMat(1+nbOrEdge, 1+nbOrEdge);
    TheMat[1][1]:=1;
    eListOrEdge:=[];
    for iOrEdge in [1..nbOrEdge]
    do
      eOrEdge:=ListOrientedEdges[iOrEdge];
      fOrEdge:=OnTuples(eOrEdge, eGen);
      pos:=Position(ListOrientedEdges, fOrEdge);
      Add(eListOrEdge, pos);
      TheMat[1+iOrEdge][1+pos]:=1;
    od;
    ePermOrEdge:=PermList(eListOrEdge);
    Add(ListPermOrEdge, ePermOrEdge);
    Add(ListMatrGens, TheMat);
  od;
  GRPoredge:=Group(ListPermOrEdge);
  #
  # The symmetries, from oriented switchings
  #
  Overt:=Orbits(GRPvert, [1..n], OnPoints);
  for eO in Overt
  do
    iVert:=eO[1];
    #
    TheMat:=NullMat(1+nbOrEdge, 1+nbOrEdge);
    TheMat[1][1]:=1;
    for kOrEdge in [1..nbOrEdge]
    do
      gOrEdge:=ListOrientedEdges[kOrEdge];
      pos:=Position(gOrEdge, iVert);
      if pos=fail then
        TheMat[1+kOrEdge][1+kOrEdge]:=1;
      else
        fOrEdge:=Reversed(gOrEdge);
        jOrEdge:=Position(ListOrientedEdges, fOrEdge);
        TheMat[1+kOrEdge][1+jOrEdge]:=-1;
        TheMat[1][1+jOrEdge]:=1;
      fi;
    od;
    Add(ListMatrGens, TheMat);
  od;
  GRPmatr:=Group(ListMatrGens);
  #
  # function creating the cut
  #
  GetOrientedMulticutGraph:=function(ListSets)
    local eVectStatus, iSet, eSet, eVect, iOrEdge, eOrEdge, i, j, eVal;
    eVectStatus:=ListWithIdenticalEntries(n,0);
    for iSet in [1..Length(ListSets)]
    do
      eSet:=ListSets[iSet];
      eVectStatus{eSet}:=ListWithIdenticalEntries(Length(eSet), iSet);
    od;
#    Print("eVectStatus=", eVectStatus, "\n");
    eVect:=ListWithIdenticalEntries(1+nbOrEdge,0);
    eVect[1]:=1;
    for iOrEdge in [1..nbOrEdge]
    do
      eOrEdge:=ListOrientedEdges[iOrEdge];
      i:=eOrEdge[1];
      j:=eOrEdge[2];
      if eVectStatus[i]<eVectStatus[j] then
        eVal:=1;
      else
        eVal:=0;
      fi;
      eVect[1+iOrEdge]:=eVal;
    od;
    return eVect;
  end;
  #
  # The oriented cut polytope
  #
  nbLow:=LowerInteger(n/2);
  CUTocut_exthigh:=[];
  for i in [0..n]
  do
    eSet1:=[1..i];
    eSet2:=[i+1..n];
    ListSets:=[eSet1, eSet2];
    Print("i=", i, " eSet1=", eSet1, " eSet2=", eSet2, "\n");
    eRay:=GetOrientedMulticutGraph(ListSets);
    pos:=Position(CUTocut_exthigh, eRay);
    Print("  pos=", pos, "\n");
    if pos=fail then
#      Print("eRay=", eRay, "\n");
      O:=Orbit(GRPmatr, eRay, OnPoints);
#      Print("ListSets=", ListSets, " |O|=", Length(O), "\n");
      Append(CUTocut_exthigh, O);
    fi;
  od;
  #
  # The oriented multicut polytope
  #
  OmcutComputed:=false;
  ComputeOmcutRelated:=function();
    if OmcutComputed then
      return;
    fi;
    CUTomcut_ext:=[];
    for ePartition in GenerationRamanujanPartitions(n)
    do
      eRay:=GetOrientedMulticutGraph(ePartition);
      if Position(CUTomcut_ext, eRay)=fail then
        O:=Orbit(GRPmatr, eRay, OnPoints);
        Append(CUTomcut_ext, O);
      fi;
    od;
    rankOmcut:=RankMat(CUTomcut_ext);
    if rankOmcut<>1+nbOrEdge then
      Error("Thinking error maybe or a simple bug");
    fi;
    CUTomcut_grpext:=GetPermutationGroupFromMatrixGroup(CUTomcut_ext, GRPmatr);
    CUTomcut_info:=rec(EXT:=CUTomcut_ext, GRP:=CUTomcut_grpext);
    ListRepresentativeFacetOmcut:=[];
    ListRepresentativeFacetRaw:=[];
    FuncInsertOrbitFacetOmcut:=function(eIneq)
      local eSetIncd, i, eScal, fRepr, test;
      Add(ListRepresentativeFacetRaw, eIneq);
      eSetIncd:=[];
      for i in [1..Length(CUTomcut_ext)]
      do
        eScal:=CUTomcut_ext[i]*eIneq;
        if eScal<0 then
          Error("eIneq is not a facet");
        fi;
        if eScal=0 then
          Add(eSetIncd, i);
        fi;
      od;
      if RankMat(CUTomcut_ext{eSetIncd})<nbOrEdge then
        Print("eIneq=", eIneq, " is just a valid inequality (OMCUT)\n");
        return;
      fi;
      for fRepr in ListRepresentativeFacetOmcut
      do
        test:=RepresentativeAction(CUTomcut_grpext, eSetIncd, fRepr, OnSets);
        if test<>fail then
          return;
        fi;
      od;
      Add(ListRepresentativeFacetOmcut, eSetIncd);
    end;
    for eIneq in ListRepresentativeFacetRaw
    do
      FuncInsertOrbitFacetOmcut(eIneq);
    od;
    Print("nbOrbit Facet of OMCUT=", Length(ListRepresentativeFacetOmcut), "\n");
    METomcut_info:=CMC_CreateInformation(ListRepresentativeFacetOmcut, CUTomcut_grpext, CUTomcut_ext);
    OmcutComputed:=true;
  end;
  GetOMCUT_met:=function()
    ComputeOmcutRelated();
    return METomcut_info;
  end;
  GetOMCUT_cut:=function()
    ComputeOmcutRelated();
    return CUTomcut_info;
  end;
  #
  # Creation of the permutation 
  #
  CUTocut_grpext:=GetPermutationGroupFromMatrixGroup(CUTocut_exthigh, GRPmatr);
  #
  # Creating the list of orbit of cycle and then the facets
  #
  RecOpt:=rec(TheLen:=-1,
              UseMinimumOrbit:=true,
              RequireIrreducible:=true,
              RequireIsometricCycleFixedLength:=false,
              RequireIsometric:=false);
  RecListOrbitCycle:=GRAPH_EnumerateCycles(TheGraph, GRPvert, RecOpt);
  SubsequentIdx:=function(eOpt, TheLen, iPos)
    if eOpt=0 then
      return NextIdx(TheLen,iPos);
    else
      return PrevIdx(TheLen,iPos);
    fi;
  end;
  ListRepresentativeFacetRaw:=[];
  for eRepr in RecListOrbitCycle.FinalListOrb
  do
    len:=Length(eRepr);
    for i in [1..len]
    do
      for eChoice in [0..1]
      do
        iAdj:=SubsequentIdx(eChoice, len, i);
        eIneq:=ListWithIdenticalEntries(1+nbOrEdge,0);
        eOrEdge:=[eRepr[i], eRepr[iAdj]];
        iOrEdge:=Position(ListOrientedEdges, eOrEdge);
        eIneq[1+iOrEdge]:=-1;
        for u in [1..len-1]
        do
          iNextAdj:=SubsequentIdx(eChoice, len, iAdj);
          fOrEdge:=[eRepr[iNextAdj], eRepr[iAdj]];
          jOrEdge:=Position(ListOrientedEdges, fOrEdge);
          eIneq[1+jOrEdge]:=1;
          iAdj:=iNextAdj;
        od;
        Add(ListRepresentativeFacetRaw, eIneq);
      od;
    od;
  od;
  Ooredge:=Orbits(GRPoredge, [1..nbOrEdge], OnPoints);
  for eO in Ooredge
  do
    iOrEdge:=eO[1];
    eIneq:=ListWithIdenticalEntries(1+nbOrEdge,0);
    eIneq[1+iOrEdge]:=1;
    Add(ListRepresentativeFacetRaw, eIneq);
  od;
  #
  # Determining the facets of EXTocut
  # Building the EXTocut facets and groups
  #
  eSelect:=ColumnReduction(CUTocut_exthigh).Select;
  CUTocut_ext:=List(CUTocut_exthigh, x->x{eSelect});
  ListRepresentativeFacetOcut:=[];
  FuncInsertOrbitFacetOcut:=function(eIneq)
    local eSetIncd, eCutHigh, eScal, fRepr, test;
    eSetIncd:=[];
    for i in [1..Length(CUTocut_exthigh)]
    do
      eCutHigh:=CUTocut_exthigh[i];
      eScal:=eIneq*eCutHigh;
      if eScal<0 then
        Error("Clear violation of our conventions\n");
      fi;
      if eScal=0 then
        Add(eSetIncd, i);
      fi;
    od;
    if RankMat(CUTocut_ext{eSetIncd})<Length(eSelect)-1 then
      Print("eIneq=", eIneq, " is just a valid inequality (OCUT)\n");
      return;
    fi;
    for fRepr in ListRepresentativeFacetOcut
    do
      test:=RepresentativeAction(CUTocut_grpext, eSetIncd, fRepr, OnSets);
      if test<>fail then
        return;
      fi;
    od;
    Add(ListRepresentativeFacetOcut, eSetIncd);
  end;
  for eIneq in ListRepresentativeFacetRaw
  do
    FuncInsertOrbitFacetOcut(eIneq);
  od;
  METocut_info:=CMC_CreateInformation(ListRepresentativeFacetOcut, CUTocut_grpext, CUTocut_ext);
  CUTocut_info:=rec(EXT:=CUTocut_ext, GRP:=CUTocut_grpext);
  return rec(ListOrientedEdges:=ListOrientedEdges,
             eSelect:=eSelect,
             GRPvert:=GRPvert, 
             GRPoredge:=GRPoredge, 
             METocut_info:=METocut_info,
             CUTocut_info:=CUTocut_info,
             GetOMCUT_met:=GetOMCUT_met, 
             GetOMCUT_cut:=GetOMCUT_cut);
end;







SelectionMinimalQMETelement:=function(ListElement)
  local IsFirst, eElt, nbZero, TheSum, nbZeroSel, TheSumSel, TheSelection;
  IsFirst:=true;
  for eElt in ListElement
  do
    nbZero:=Length(Filtered(eElt, x->x=0));
    TheSum:=Sum(eElt);
    if IsFirst=true then
      nbZeroSel:=nbZero;
      TheSumSel:=TheSum;
      TheSelection:=eElt;
    else
      if nbZero>nbZeroSel then
        nbZeroSel:=nbZero;
        TheSumSel:=TheSum;
        TheSelection:=eElt;
      else
        if nbZero=nbZeroSel and TheSum<TheSum then
          nbZeroSel:=nbZero;
          TheSumSel:=TheSum;
          TheSelection:=eElt;
        fi;
      fi; 
    fi;
    IsFirst:=false;
  od;
  return TheSelection;
end;

SelectionMinimalOCUTfacet:=function(eRec, ListElement)
  local IsFirst, eElt, nbZero, TheSum, nbZeroSel, TheSumSel, TheSelection, len;
  IsFirst:=true;
  len:=Length(ListElement[1]);
  for eElt in ListElement
  do
    nbZero:=Length(Filtered(eElt{eRec.eSetWeight}, x->x=0));
    TheSum:=Sum(List([1..len], x->AbsInt(eElt[x])*x));
    if IsFirst=true then
      nbZeroSel:=nbZero;
      TheSumSel:=TheSum;
      TheSelection:=eElt;
    else
      if nbZero>nbZeroSel then
        nbZeroSel:=nbZero;
        TheSumSel:=TheSum;
        TheSelection:=eElt;
      else
        if nbZero=nbZeroSel and TheSum<TheSum then
          nbZeroSel:=nbZero;
          TheSumSel:=TheSum;
          TheSelection:=eElt;
        fi;
      fi; 
    fi;
    IsFirst:=false;
  od;
  return TheSelection;
end;




PrintQMETelement:=function(output, eRec, eRay)
  local n, eMat, i, j, eC, pos, eRecF;
  n:=eRec.n;
  eMat:=NullMat(n,n);
  for i in [1..n]
  do
    for j in [1..n]
    do
      if i<>j then
        eC:=[i, j];
        pos:=Position(eRec.ListC, eC);
        eMat[i][j]:=eRay[pos];
      fi;
    od;
  od;
  eRecF:=RemoveFractionMatrixPlusCoef(eMat);
  PrintRationalMatrix(output, eRecF.TheMat);
  AppendTo(output, "   denominator=", eRecF.TheMult, "\n");
end;


SortingOrbit:=function(ListOrb, GRP)
  local nbOrb, ListInc, ListOrdStab, eOrb, eStab, ListDiscriminant, eReordPerm;
  nbOrb:=Length(ListOrb);
  ListInc:=List(ListOrb, Length);
  ListOrdStab:=[];
  for eOrb in ListOrb
  do
    eStab:=Stabilizer(GRP, eOrb, OnSets);
    Add(ListOrdStab, Order(eStab));
  od;
  ListDiscriminant:=List([1..nbOrb], x->[
    1/ListInc[x],
    1/ListOrdStab[x]
   ]);
  eReordPerm:=SortingPerm(ListDiscriminant);
  return Permuted(ListOrb, eReordPerm);
end;

Cone_GetSkeleton:=function(n)
  local eRec, GRP, TheSkel, ListNeg, O, eO, eVert, eSet, eNeg;
  eRec:=Cone_OCUT(n);
  GRP:=LinPolytope_Automorphism(eRec.EXT);
  TheSkel:=SkeletonGraph(GRP, eRec.EXT, []);
  O:=Orbits(GRP, [1..Length(eRec.EXT)], OnPoints);
  ListNeg:=[];
  for eO in O
  do
    eVert:=eO[1];
    eSet:=Difference([1..Length(eRec.EXT)], [eVert]);
    eNeg:=Difference(eSet, Adjacency(TheSkel, eVert));
    Add(ListNeg, eNeg);
  od;
  return rec(TheSkel:=TheSkel, ListNeg:=ListNeg);
end;





Cone_GetFacetDescription:=function(eRec, eInc)
  local EXTred;
  EXTred:=List(eRec.EXT, x->Cone_GetWeightedPresentation(eRec, x));
  return __FindFacetInequality(EXTred, eInc);
end;


ConePoly_PartialMetrics:=function(n)
  local ListSymbol, i, j, k, CanSymbol, GetPosition, nbSymb, ListIneqCone, eSymb1, pos1, eVect, eSymb2, pos2, posIJ, posIK, posJK, posII, posJJ, posKK, ListIneqPoly, eSet;
  ListSymbol:=[];
  for i in [1..n]
  do
    Add(ListSymbol, [i,i]);
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(ListSymbol, [i,j]);
    od;
  od;
  CanSymbol:=function(eSymb)
    local i, j;
    i:=eSymb[1];
    j:=eSymb[2];
    if i<j then
      return [i,j];
    fi;
    return [j,i];
  end;
  GetPosition:=function(eSymb)
    return Position(ListSymbol, CanSymbol(eSymb));
  end;
  nbSymb:=Length(ListSymbol);
  ListIneqCone:=[];
  ListIneqPoly:=[];
  for i in [1..n]
  do
    eSymb1:=[i,i];
    pos1:=GetPosition(eSymb1);
    eVect:=ListWithIdenticalEntries(nbSymb,0);
    eVect[pos1]:=1;
    Add(ListIneqCone, eVect);
    Add(ListIneqPoly, Concatenation([0],eVect));
    for j in Difference([1..n],[i])
    do
      eSymb2:=[i,j];
      pos2:=GetPosition(eSymb2);
      eVect:=ListWithIdenticalEntries(nbSymb,0);
      eVect[pos2]:=1;
      eVect[pos1]:=-1;
      Add(ListIneqCone, eVect);
      Add(ListIneqPoly, Concatenation([0],eVect));
      eVect:=ListWithIdenticalEntries(nbSymb+1,0);
      eVect[1]:=1;
      eVect[1+pos2]:=-1;
      eVect[1+pos1]:=1;
      Add(ListIneqPoly, eVect);
    od;
  od;
  for i in [1..n-1]
  do
    for k in [i+1..n]
    do
      posIK:=GetPosition([i,k]);
      for j in Difference([1..n], Set([i,k]))
      do
        posIJ:=GetPosition([i,j]);
        posJK:=GetPosition([j,k]);
        posJJ:=GetPosition([j,j]);
        eVect:=ListWithIdenticalEntries(nbSymb,0);
        eVect[posIJ]:=1;
        eVect[posJK]:=1;
        eVect[posJJ]:=-1;
        eVect[posIK]:=-1;
        Add(ListIneqCone, eVect);
        Add(ListIneqPoly, Concatenation([0],eVect));
      od;
    od;
  od;
  for eSet in Combinations([1..n], 3)
  do
    i:=eSet[1];
    j:=eSet[2];
    k:=eSet[3];
    posIJ:=GetPosition([i,j]);
    posIK:=GetPosition([i,k]);
    posJK:=GetPosition([j,k]);
    posII:=GetPosition([i,i]);
    posJJ:=GetPosition([j,j]);
    posKK:=GetPosition([k,k]);
    eVect:=ListWithIdenticalEntries(1+nbSymb,0);
    eVect[1]:=2;
    eVect[1+posIJ]:=-1;
    eVect[1+posIK]:=-1;
    eVect[1+posJK]:=-1;
    eVect[1+posII]:=1;
    eVect[1+posJJ]:=1;
    eVect[1+posKK]:=1;
    Add(ListIneqPoly, eVect);
  od;
  return rec(ListIneqCone:=ListIneqCone,
             ListIneqPoly:=ListIneqPoly);
end;


GetAllPartitions_Kset:=function(n,k)
  local GRP, TheList, TotalListPartition, eEnt, eVect, idx, eSize, iter, H, v, O;
  GRP:=SymmetricGroup([1..n]);
  TheList:=Filtered(ListOfPartitions(n,n), x->Sum(x)=k);
  TotalListPartition:=[];
  for eEnt in TheList
  do
    eVect:=[];
    idx:=0;
    for eSize in [1..n]
    do
      for iter in [1..eEnt[eSize]]
      do
        H:=[];
	for v in [1..eSize]
	do
	  idx:=idx+1;
	  Add(H, idx);
	od;
	Add(eVect, H);
      od;
    od;
    O:=Orbit(GRP, eVect, OnSetsSets);
    Append(TotalListPartition, O);
  od;
  return TotalListPartition;
end;






HCUT_Cone:=function(n,s)
  local EXTsymb, ListIndex, EXT, eEXTsymb, eVect, iSet, uSet, eEXT, eIndex, ListMatch, eVal, pos, insVal;
  EXTsymb:=GetAllPartitions_Kset(n,s+1);
  ListIndex:=Combinations([1..n],s+1);
  EXT:=[];
  for eEXTsymb in EXTsymb
  do
    eVect:=ListWithIdenticalEntries(n,0);
    for iSet in [1..Length(eEXTsymb)]
    do
      uSet:=eEXTsymb[iSet];
      eVect{uSet}:=ListWithIdenticalEntries(Length(uSet),iSet);
    od;
    eEXT:=[];
    for eIndex in ListIndex
    do
      ListMatch:=ListWithIdenticalEntries(s+1,0);
      for eVal in eIndex
      do
        pos:=eVect[eVal];
        ListMatch[pos]:=1;
      od;
      if Sum(ListMatch)=s+1 then
        insVal:=1;
      else
        insVal:=0;
      fi;
      Add(eEXT, insVal);
    od;
    Add(EXT, eEXT);
  od;
  return EXT;
end;
