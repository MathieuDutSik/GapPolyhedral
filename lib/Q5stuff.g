Q5_FieldProduct:=function(eElt1, eElt2)
  local p1, q1, p2, q2;
  p1:=eElt1[1];
  q1:=eElt1[2];
  p2:=eElt2[1];
  q2:=eElt2[2];
  return [p1*p2+5*q1*q2, p1*q2+p2*q1];
end;


Q5_FieldSum:=function(eElt1, eElt2)
  local p1, q1, p2, q2;
  p1:=eElt1[1];
  q1:=eElt1[2];
  p2:=eElt2[1];
  q2:=eElt2[2];
  return [p1+p2, q1+q2];
end;

Q5_ScalarProd:=function(V1, V2)
  local Sum, iCol;
  Sum:=[0,0];
  for iCol in [1..Length(V1)]
  do
    Sum:=Q5_FieldSum(Sum, Q5_FieldProduct(V1[iCol], V2[iCol]));
  od;
  return Sum;
end;

Q5_SignGen:=function(V)
  local SED, ListV, eSED, Vnew, iCol;
  SED:=BuildSet(Length(V),[-1,1]);
  ListV:=[];
  for eSED in SED
  do
    Vnew:=[];
    for iCol in [1..Length(V)]
    do
      Vnew[iCol]:=eSED[iCol]*V[iCol];
    od;
    Add(ListV, Vnew);
  od;
  return ListV;
end;


Q5_DistanceVector:=function(V1, V2)
  local Vdiff;
  Vdiff:=V1-V2;
  return Sum(List([1..Length(V1)], x->Vdiff[x]*Vdiff[x]));
end;


Q5_FindHyperplan:=function(Vset)
  local Bset, EQset, V, EQ1, EQ2, i, eElt, Sol;
  Bset:=[];
  EQset:=[];
  for V in Vset
  do
    Add(Bset, -1);
    Add(Bset, 0);
    EQ1:=[];
    EQ2:=[];
    for i in [1..4]
    do
      eElt:=V[i];
      Add(EQ1, eElt[1]);
      Add(EQ1, 5*eElt[2]);
      Add(EQ2, eElt[2]);
      Add(EQ2, eElt[1]);
    od;
    Add(EQset, EQ1);
    Add(EQset, EQ2);
  od;
  Sol:=SolutionMat(TransposedMat(EQset), Bset);
  if Sol=fail then 
    return fail;
  else
    return [[Sol[1],Sol[2]],[Sol[3],Sol[4]],[Sol[5],Sol[6]],[Sol[7],Sol[8]]];
  fi;
end;






Q5_TestIncidence:=function(HPL, V)
  local ESE;
  ESE:=[1,0]+Q5_ScalarProd(HPL, V);
  if ESE=[0,0] then
    return true;
  else
    return false;
  fi;
end;


Q5_TestPositivity:=function(HPL, V)
  local ESE;
  ESE:=[1,0]+Q5_ScalarProd(HPL, V);
  if ESE<>[0,0] and QN_IsPositive(5, ESE)=false then
    return false;
  else
    return true;
  fi;
end;


Q5_FindMinimum:=function(ListElement)
  local Mini, iElt;
  Mini:=ListElement[1];
  for iElt in [2..Length(ListElement)]
  do
    if QN_IsPositive(5, ListElement[iElt]-Mini)=false then
      Mini:=ListElement[iElt];
    fi;
  od;
  return Mini;
end;


#
#
# creation of the list of vertices


Q5_GetPolyhedraH4:=function()
  local Q5_tau, Q5_tau2, Q5_tauInv, Q5_tauInv2, ListVectors, Sym4, ListPos, u, Alt4, DistSet, ListSet, ePt, Stab2, TotalStab, GRA, ListGRA, TotGRP, eEdge, iVert, GRP15_extended, TheOrb, eEquivH3, eEquivH4, DistMatFifteen_Cyc, GRP15_dist, ConjDistMatFifteen_Cyc, ListVal15_Cyc, eVal, iRep, eScal, eNormH3, ListRepH3, nbPairH3, DistMatFifteen_CycNoSquare, ListNormH3, Stab1, Stab2red, GRP60_extended, eSet, nbPair, i, jRep, FuncTransform, ListRep, GRP60_dist, DistMat60_Cyc, ConjDistMat60_Cyc, RetMat, ePerm, pos1, eValNonSqr1, pos2, Stab1red, ListVal60_Cyc, ListNonRat, eValNonSqr2, DistMat60_CycNoSquare, eNorm, eList, ListVert120Cell_Cyc, eVert, ListPermGens, eGen, FindPos, O_Cyc, GRPanti, testEquality, nbV, GRP60, ListNorm, GRP120, ListFacet, eInt, eSum, eVect, pos, O_Q5, DistMat120, j, ListVert120Cell_Q5, eFacet, SymGrp, FACbegin, HPlan, ReprFacet, PL, Gra, iCol, jCol, TheMini, GRP120_dist, WeylGroupH4, ListGeneratorsH4, eMat, ListDegree, EXT600, EXT120, eGRP5, eElt1, eElt2, eElt3, eElt4, eClique, ListClique, FuncExpressAllElement, eStab, eStab3, eStab2, ListPermGens120, ListCoxeterGens, phi, phiRev;
  Q5_tau:=1/2 + Sqrt(5)*1/2;
  Q5_tau2:=Q5_tau*Q5_tau;
  Q5_tauInv:=-1/2 + Sqrt(5)/2;
  Q5_tauInv2:=Q5_tauInv*Q5_tauInv;
  ListVectors:=[];
  ListPos:=Q5_SignGen([2,2,0,0]);
  ListPos:=Union(ListPos, Q5_SignGen([Sqrt(5),1,1,1]));
  ListPos:=Union(ListPos, Q5_SignGen([Q5_tau, Q5_tau, Q5_tau, Q5_tauInv2]));
  ListPos:=Union(ListPos, Q5_SignGen([Q5_tau2, Q5_tauInv, Q5_tauInv, Q5_tauInv]));
  Sym4:=SymmetricGroup([1..4]);
  for u in ListPos
  do
    ListVectors:=Union(ListVectors, Orbit(Sym4, u, Permuted));
  od;
  #
  ListPos:=Q5_SignGen([Q5_tau2, Q5_tauInv2, 1, 0]);
  ListPos:=Union(ListPos, Q5_SignGen([Sqrt(5),Q5_tauInv, Q5_tau, 0]));
  ListPos:=Union(ListPos, Q5_SignGen([2,1,Q5_tau, Q5_tauInv]));
  Alt4:=AlternatingGroup([1..4]);
  for u in ListPos
  do
    ListVectors:=Union(ListVectors, Orbit(Alt4, u, Permuted));
  od;
  Print("|ListVectors|=", Length(ListVectors), "\n");
  #
  DistSet:=[];
  for i in [2..Length(ListVectors)]
  do
    AddSet(DistSet, Q5_DistanceVector(ListVectors[1], ListVectors[i]));
  od;
  Print("|DistSet|=", Length(DistSet), "\n");
  #
  TheMini:=Q5_FindMinimum(DistSet);
  Print("TheMini=", TheMini, "\n");
  #
  Gra:=NullGraph(Group(()), 600);
  for iCol in [1..600]
  do
    for jCol in [1..600]
    do
      if Q5_DistanceVector(ListVectors[iCol], ListVectors[jCol])=TheMini then
        AddEdgeOrbit(Gra, [iCol, jCol]);
      fi;
    od;
  od;
  ListDegree:=List([1..600], x->Length(Adjacency(Gra, x)));
  Print("Collected(ListDegree)=", Collected(ListDegree), "\n");
  #
  SymGrp:=AutGroupGraph(Gra);
  Print("|SymGrp|=", Order(SymGrp), "\n");
  #
  PL:=Adjacency(Gra, 1);
  EXT600:=List(ListVectors, x->Concatenation([1], x));
  FACbegin:=[EXT600[1], EXT600[PL[1]], EXT600[PL[2]], EXT600[PL[3]]];
  HPlan:=NullspaceMat(TransposedMat(FACbegin))[1];
  ReprFacet:=Filtered([1..600], x->HPlan*EXT600[x]=0);
  ListFacet:=Orbit(SymGrp, ReprFacet, OnSets);
  ListVert120Cell_Cyc:=[];
  EXT120:=List(ListVert120Cell_Cyc, x->Concatenation([1], x));
  for eFacet in ListFacet
  do
    eSum:=Sum(ListVectors{eFacet});
    Add(ListVert120Cell_Cyc, eSum);
  od;
#  Print("|ListVert120Cell_Cyc|=", Length(ListVert120Cell_Cyc), "\n");
  GRA:=NullGraph(Group(()), 120);
  for i in [1..119]
  do
    for j in [i+1..120]
    do
      eInt:=Intersection(ListFacet[i], ListFacet[j]);
      if Length(eInt)=5 then
        AddEdgeOrbit(GRA, [i,j]);
        AddEdgeOrbit(GRA, [j,i]);
      fi;
    od;
  od;
  GRP120:=AutGroupGraph(GRA);
#  Print("|GRP120|=", Order(GRP120), "\n");
  ListClique:=CompleteSubgraphsOfGivenSize(GRA, 4);
  eClique:=ListClique[1];
  eGRP5:=GRP120;
  for i in [1..3]
  do
    eGRP5:=Stabilizer(eGRP5, eClique[i], OnPoints);
  od;
  eElt4:=GeneratorsOfGroup(eGRP5)[1];
  #
  eStab:=Stabilizer(GRP120, eClique, OnSets);
  eStab2:=Stabilizer(eStab, eClique[4], OnPoints);
  eStab3:=Stabilizer(eStab2, eClique[3], OnPoints);
  eElt1:=GeneratorsOfGroup(eStab3)[1];
  #
  eStab2:=Stabilizer(eStab, eClique[1], OnPoints);
  eStab3:=Stabilizer(eStab2, eClique[4], OnPoints);
  eElt2:=GeneratorsOfGroup(eStab3)[1];
  #
  eStab2:=Stabilizer(eStab, eClique[1], OnPoints);
  eStab3:=Stabilizer(eStab2, eClique[2], OnPoints);
  eElt3:=GeneratorsOfGroup(eStab3)[1];
  # those above form a coxeter generating set.
  ListCoxeterGens:=[eElt1, eElt2, eElt3, eElt4];
  #
  # 
  FuncExpressAllElement:=function()
    local ListElement, ListSeq, ListStatus, eElt, nbElt, pos, IsFinished, i, eProd, iElt;
    ListElement:=[];
    ListStatus:=[];
    ListSeq:=[];
    for eElt in GRP120
    do
      Add(ListElement, eElt);
      Add(ListStatus, 0);
      Add(ListSeq, []); 
    od;
    nbElt:=Length(ListElement);
    pos:=Position(ListElement, ());
    ListStatus[pos]:=1;
    while(true)
    do
      IsFinished:=true;
      for iElt in [1..nbElt]
      do
        if ListStatus[iElt]=1 then
          ListStatus[iElt]:=-1;
          eElt:=ListElement[iElt];
          IsFinished:=false;
          for i in [1..4]
          do
            eProd:=eElt*ListCoxeterGens[i];
            pos:=Position(ListElement, eProd);
            if ListStatus[pos]=0 then
              ListStatus[pos]:=1;
              ListSeq[pos]:=Concatenation(ListSeq[iElt], [i]);
            fi;
          od;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    return rec(ListElement:=ListElement, ListSeq:=ListSeq);
  end;
  nbV:=120;
  DistMat120:=NullMat(nbV, nbV);
  for i in [1..nbV-1]
  do
    for j in [i+1..nbV]
    do
      eScal:=ListVert120Cell_Cyc[i]*ListVert120Cell_Cyc[j];
      DistMat120[i][j]:=eScal;
      DistMat120[j][i]:=eScal;
    od;
  od;
  GRP120_dist:=AutomorphismGroupEdgeColoredGraph(DistMat120);
  testEquality:=GRP120_dist=GRP120;
  if testEquality=false then
    Error("We have inconsistency");
  fi;
  GRPanti:=Group([-IdentityMat(4)]);
  O_Cyc:=Orbits(GRPanti, ListVert120Cell_Cyc);
  O_Q5:=List(O_Cyc, x->ListVert120Cell_Cyc[Position(O_Cyc, x)]);
  ListRep:=List(O_Cyc, x->x[1]);
  FindPos:=function(eVect)
    local iPos;
    for iPos in [1..Length(O_Cyc)]
    do
      if Position(O_Cyc[iPos], eVect)<>fail then
        return iPos;
      fi;
    od;
  end;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRP120)
  do
    eList:=[];
    for eVert in ListRep
    do
      pos:=Position(ListVert120Cell_Cyc, eVert);
      Add(eList, FindPos(ListVert120Cell_Cyc[OnPoints(pos, eGen)]));
    od;
    Add(ListPermGens, PermList(eList));
  od;
  GRP60:=Group(ListPermGens);
  nbPair:=60;
  ListNorm:=List(ListRep, x->x*x);
  eNorm:=ListNorm[1];
  DistMat60_Cyc:=NullMat(nbPair, nbPair);
  DistMat60_CycNoSquare:=NullMat(nbPair, nbPair);
  for iRep in [1..nbPair-1]
  do
    for jRep in [iRep..nbPair]
    do
      eScal:=ListRep[iRep]*ListRep[jRep];
      eVal:=eScal/eNorm;
      DistMat60_Cyc[iRep][jRep]:=eVal*eVal;
      DistMat60_Cyc[jRep][iRep]:=eVal*eVal;
      DistMat60_CycNoSquare[iRep][jRep]:=eVal;
      DistMat60_CycNoSquare[jRep][iRep]:=eVal;
    od;
  od;
  GRP60_dist:=AutomorphismGroupEdgeColoredGraph(DistMat60_Cyc);
  #TheComp:=ReprAct_FullEnumeration(ListRep, GRP60);
  ListVal60_Cyc:=List(Collected(DistMat60_Cyc[1]), x->x[1]);
  ListNonRat:=Filtered([1..Length(ListVal60_Cyc)], x->IsRat(ListVal60_Cyc[x])=false);
  ePerm:=(ListNonRat[1], ListNonRat[2]);
  pos1:=Position(DistMat60_Cyc[1], ListVal60_Cyc[ListNonRat[1]]);
  pos2:=Position(DistMat60_Cyc[1], ListVal60_Cyc[ListNonRat[2]]);
  eValNonSqr1:=DistMat60_CycNoSquare[1][pos1];
  eValNonSqr2:=DistMat60_CycNoSquare[1][pos2];
  # quick analysis gives
  # eValNonSqr1,2=(-1 +-sqrt(5))/4
  FuncTransform:=function(INPmat)
    local nbPair, RetMat, i, j, eVal, pos, jpos;
    nbPair:=Length(INPmat);
    RetMat:=NullMat(nbPair, nbPair);
    for i in [1..nbPair]
    do
      for j in [1..nbPair]
      do
        eVal:=INPmat[i][j];
        pos:=Position(ListVal60_Cyc, eVal);
        jpos:=OnPoints(pos, ePerm);
        RetMat[i][j]:=ListVal60_Cyc[jpos];
      od;
    od;
    return RetMat;
  end;
  ConjDistMat60_Cyc:=FuncTransform(DistMat60_Cyc);
  eEquivH4:=IsIsomorphicEdgeColoredGraph(DistMat60_Cyc, ConjDistMat60_Cyc);
  GRP60_extended:=Group(Concatenation(GeneratorsOfGroup(GRP60_dist), [PermList(eEquivH4)]));
  ListSet:=[];
  for i in [1..nbPair]
  do
    eSet:=Filtered([1..nbPair], x->ListRep[x]*ListRep[i]=0);
    Add(ListSet, eSet);
  od;
  Stab1:=Stabilizer(GRP60_dist, ListSet[1], OnSets);
  Stab2:=Stabilizer(GRP60_extended, ListSet[1], OnSets);
  Stab1red:=SecondReduceGroupAction(Stab1, ListSet[1]);
  Stab2red:=SecondReduceGroupAction(Stab1, ListSet[1]);
  ListRepH3:=ListRep{ListSet[1]};
  nbPairH3:=Length(ListRepH3);
  ListNormH3:=List(ListRepH3, x->x*x);
  eNormH3:=ListNormH3[1];
  DistMatFifteen_Cyc:=NullMat(nbPairH3, nbPairH3);
  DistMatFifteen_CycNoSquare:=NullMat(nbPairH3, nbPairH3);
  for iRep in [1..nbPairH3-1]
  do
    for jRep in [iRep..nbPairH3]
    do
      eScal:=ListRepH3[iRep]*ListRepH3[jRep];
      eVal:=eScal/eNormH3;
      DistMatFifteen_Cyc[iRep][jRep]:=eVal*eVal;
      DistMatFifteen_Cyc[jRep][iRep]:=eVal*eVal;
      DistMatFifteen_CycNoSquare[iRep][jRep]:=eVal;
      DistMatFifteen_CycNoSquare[jRep][iRep]:=eVal;
    od;
  od;
  ListVal15_Cyc:=List(Collected(DistMatFifteen_Cyc[1]), x->x[1]);
  ConjDistMatFifteen_Cyc:=FuncTransform(DistMatFifteen_Cyc);
  GRP15_dist:=AutomorphismGroupEdgeColoredGraph(DistMatFifteen_Cyc);
  eEquivH3:=IsIsomorphicEdgeColoredGraph(DistMatFifteen_Cyc, ConjDistMatFifteen_Cyc);
  GRP15_extended:=Group(Concatenation(GeneratorsOfGroup(GRP15_dist), [PermList(eEquivH3)]));
  ListGRA:=[];
  for iVert in [2,4,5]
  do
    GRA:=NullGraph(Group(()), 15);
    TheOrb:=Orbit(GRP15_extended, [1,iVert], OnSets);
    for eEdge in TheOrb
    do
      AddEdgeOrbit(GRA, eEdge);
      AddEdgeOrbit(GRA, Reversed(eEdge));
    od;
    TotGRP:=AutGroupGraph(GRA);
    Add(ListGRA, rec(GRA:=GRA, TotGRP:=TotGRP));
  od;
  TotalStab:=Group(GeneratorsOfGroup(Stab2));
  for ePt in ListSet[1]
  do
    TotalStab:=Stabilizer(TotalStab, ePt, OnPoints);
  od;
  ListGeneratorsH4:=[];
  ListPermGens120:=GeneratorsOfGroup(GRP120_dist);
  for eGen in ListPermGens120
  do
    eMat:=FindTransformation(ListVert120Cell_Cyc, ListVert120Cell_Cyc, eGen);
    Add(ListGeneratorsH4, eMat);
  od;
  WeylGroupH4:=Group(ListGeneratorsH4);
  phi:=GroupHomomorphismByImagesNC(GRP120_dist, WeylGroupH4, ListPermGens120, ListGeneratorsH4);
  phiRev:=GroupHomomorphismByImagesNC(WeylGroupH4, GRP120_dist, ListGeneratorsH4, ListPermGens120);
  return rec(EXT120:=EXT120, EXT600:=EXT600, 
             RootSystemH4:=ListVert120Cell_Cyc, 
             FuncExpressAllElement:=FuncExpressAllElement, 
             ListCoxeterGens:=ListCoxeterGens,
             PermGroup120:=GRP120_dist, 
             phi:=phi, 
             phiRev:=phiRev, 
             WeylGroupH4:=WeylGroupH4);
end;


Q5_GetPolyhedraH3:=function()
  local Q5_tau, ListPos, u, ListVert12Cell_Q5, eVectPair, eVect, eVal, ListScal, Alt3, GRP1, nbV, ListGeneratorsH3, WeylGroupH3, eGen, eMat, ListRoors, i, j, eScal, ListRoots;
  Q5_tau:=1/2 + Sqrt(5)/2;
  ListPos:=Q5_SignGen([Q5_tau, 1, 0]);
  Alt3:=AlternatingGroup(3);
  ListVert12Cell_Q5:=[];
  for u in ListPos
  do
    ListVert12Cell_Q5:=Union(ListVert12Cell_Q5, Orbit(Alt3, u, Permuted));
  od;
  nbV:=Length(ListVert12Cell_Q5);
  ListScal:=List([1..nbV], x->ListVert12Cell_Q5[x]*ListVert12Cell_Q5[1]);
  GRP1:=__TheCore_Automorphism(ListVert12Cell_Q5);
#  Print("|GRP1|=", Order(GRP1), "\n");
#  Print("CollScal=", Collected(ListScal), "\n");
  eScal:=-E(5)^2-E(5)^3;
  ListRoots:=[];
  for i in [1..nbV-1]
  do
    for j in [i+1..nbV]
    do
      if ListVert12Cell_Q5[i]*ListVert12Cell_Q5[j]=eScal then
        Add(ListRoots, ListVert12Cell_Q5[i]+ListVert12Cell_Q5[j]);
      fi;
    od;
  od;
  ListGeneratorsH3:=[];
  for eGen in GeneratorsOfGroup(GRP1)
  do
    eMat:=FindTransformation(ListVert12Cell_Q5, ListVert12Cell_Q5, eGen);
    Add(ListGeneratorsH3, eMat);
  od;
  WeylGroupH3:=Group(ListGeneratorsH3);
  return rec(WeylGroupH3:=WeylGroupH3, 
             ListVert12Cell_Q5:=ListVert12Cell_Q5);
end;
