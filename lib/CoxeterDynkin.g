__G2fin_diagram:=function()
  local TheMat;
  TheMat:=[[6]];
  return rec(TheMat:=TheMat, type:="fin", eNameHumph:="G6", eNameLatexHumph:="G_6", eNameConway:="g6", eNameLatexConway:="g_6");
end;


__ZerMat:=function(n)
  local TheMat, i, j;
  TheMat:=NullMat(n,n);
  for i in [1..n]
  do
    TheMat[i][i]:=1;
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      TheMat[i][j]:=2;
      TheMat[j][i]:=2;
    od;
  od;
  return TheMat;
end;


__G2aff_diagram:=function()
  local TheMat;
  TheMat:=__ZerMat(3);
  TheMat[1][2]:=3;
  TheMat[2][1]:=3;
  TheMat[2][3]:=6;
  TheMat[3][2]:=6;
  return rec(TheMat:=TheMat, type:="aff", eNameHumph:="tildeG2", eNameLatexHumph:="\\tilde{G}_2", eNameConway:="G2", eNameLatexConway:="G_2");
end;



__F4fin_diagram:=function()
  local TheMat;
  TheMat:=__ZerMat(4);
  TheMat[1][2]:=3;
  TheMat[2][1]:=3;
  TheMat[2][3]:=4;
  TheMat[3][2]:=4;
  TheMat[3][4]:=3;
  TheMat[4][3]:=3;
  return rec(TheMat:=TheMat, type:="fin", eNameHumph:="F4", eNameLatexHumph:="F_4", eNameConway:="f4", eNameLatexConway:="f_4");
end;




__F4aff_diagram:=function()
  local TheMat;
  TheMat:=__ZerMat(5);
  TheMat[1][2]:=3;
  TheMat[2][1]:=3;
  TheMat[2][3]:=4;
  TheMat[3][2]:=4;
  TheMat[3][4]:=3;
  TheMat[4][3]:=3;
  TheMat[5][4]:=3;
  TheMat[4][5]:=3;
  return rec(TheMat:=TheMat, type:="aff", eNameHumph:="tildeF4", eNameLatexHumph:="\\tilde{F}_4", eNameConway:="F4", eNameLatexConway:="F_4");
end;



__E6fin_diagram:=function()
  local TheMat, ListEdge, eEdge, ePerm;
  TheMat:=__ZerMat(6);
  ListEdge:=[[1,2],[2,3],[3,4],[4,5],[3,6]];
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  ePerm:=(1,5)(2,4);
  return rec(TheMat:=TheMat, type:="fin", ePerm:=ePerm, eNameHumph:="E6", eNameLatexHumph:="E_6", eNameConway:="e6", eNameLatexConway:="e_6");
end;

__E6aff_diagram:=function()
  local TheMat, ListEdge, eEdge;
  TheMat:=__ZerMat(7);
  ListEdge:=[[1,2],[2,3],[3,4],[4,5],[3,6],[6,7]];
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  return rec(TheMat:=TheMat, type:="aff", eNameHumph:="tildeE6", eNameLatexHumph:="\\tilde{E}_6", eNameConway:="E6", eNameLatexConway:="E_6");
end;


__E7fin_diagram:=function()
  local TheMat, ListEdge, eEdge;
  TheMat:=__ZerMat(7);
  ListEdge:=[[1,2],[2,3],[3,4],[4,5],[3,6],[5,7]];
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  return rec(TheMat:=TheMat, type:="fin", ePerm:=(), eNameHumph:="E7", eNameLatexHumph:="E_7", eNameConway:="e7", eNameLatexConway:="e_7");
end;

__E7aff_diagram:=function()
  local TheMat, ListEdge, eEdge;
  TheMat:=__ZerMat(8);
  ListEdge:=[[1,2],[2,3],[3,4],[4,5],[3,6],[5,7],[1,8]];
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  return rec(TheMat:=TheMat, type:="aff", ePerm:=(), eNameHumph:="tildeE7", eNameLatexHumph:="\\tilde{E}_7", eNameConway:="E7", eNameLatexConway:="E_7");
end;





__E8fin_diagram:=function()
  local TheMat, ListEdge, eEdge;
  TheMat:=__ZerMat(8);
  ListEdge:=[[1,2],[2,3],[3,4],[4,5],[3,6],[5,7],[7,8]];
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  return rec(TheMat:=TheMat, type:="fin", ePerm:=(), eNameHumph:="E8", eNameLatexHumph:="E_8", eNameConway:="e8", eNameLatexConway:="e_8");
end;


__E8aff_diagram:=function()
  local TheMat, ListEdge, eEdge;
  TheMat:=__ZerMat(9);
  ListEdge:=[[1,2],[2,3],[3,4],[4,5],[3,6],[5,7],[7,8],[8,9]];
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  return rec(TheMat:=TheMat, type:="aff", eNameHumph:="tildeE8", eNameLatexHumph:="\\tilde{E}_8", eNameConway:="E8", eNameLatexConway:="E_8");
end;


__Anfin_diagram:=function(n)
  local TheMat, ListEdge, i, ePerm, eEdge;
  TheMat:=__ZerMat(n);
  ListEdge:=[];
  for i in [1..n-1]
  do
    Add(ListEdge, [i,i+1]);
  od;
  ePerm:=PermList(Reversed([1..n]));
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  return rec(TheMat:=TheMat, ePerm:=ePerm, type:="fin", 
eNameHumph:=Concatenation("A", String(n)), 
eNameLatexHumph:=Concatenation("A_{", String(n),"}"), 
eNameConway:=Concatenation("a", String(n)), 
eNameLatexConway:=Concatenation("a_{", String(n),"}"));
end;

__Anaff_diagram:=function(n)
  local TheMat, ListEdge, i, eEdge;
  if n=1 then
    return rec(type:="aff", eNameHumph:="tildeA1", eNameLatexHumph:="\\tilde{A}_1", eNameConway:="A1", eNameLatexConway:="A_1", 
TheMat:=[ [ 1, "infty" ], [ "infty", 1 ] ]);
  fi;
  TheMat:=__ZerMat(n+1);
  ListEdge:=[];
  for i in [1..n+1]
  do
    Add(ListEdge, [i,NextIdx(n+1,i)]);
  od;
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  return rec(TheMat:=TheMat, type:="aff", 
eNameHumph:=Concatenation("tildeA", String(n)), 
eNameLatexHumph:=Concatenation("\\tilde{A}_{", String(n),"}"), 
eNameConway:=Concatenation("A", String(n)), 
eNameLatexConway:=Concatenation("A_{", String(n), "}"));
end;






__Dnfin_diagram:=function(n)
  local TheMat, ListEdge, i, ePerm, eEdge;
  TheMat:=__ZerMat(n);
  ListEdge:=[[1,3],[2,3]];
  for i in [3..n-1]
  do
    Add(ListEdge, [i,i+1]);
  od;
  if n mod 2=0 then
    ePerm:=();
  else
    ePerm:=(1,2);
  fi;
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  return rec(TheMat:=TheMat, ePerm:=ePerm, type:="fin",  
eNameHumph:=Concatenation("D", String(n)), 
eNameLatexHumph:=Concatenation("D_{", String(n),"}"), 
eNameConway:=Concatenation("d", String(n)), 
eNameLatexConway:=Concatenation("d_{", String(n), "}"));
end;


__Dnaff_diagram:=function(n)
  local TheMat, ListEdge, i, eEdge;
  TheMat:=__ZerMat(n+1);
  ListEdge:=[[1,3],[2,3]];
  for i in [3..n-2]
  do
    Add(ListEdge, [i,i+1]);
  od;
  Add(ListEdge, [n-1,n]);
  Add(ListEdge, [n-1,n+1]);
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  return rec(TheMat:=TheMat, type:="aff", 
eNameHumph:=Concatenation("tildeD", String(n)), 
eNameLatexHumph:=Concatenation("\\tilde{D}_{", String(n),"}"), 
eNameConway:=Concatenation("D", String(n)), 
eNameLatexConway:=Concatenation("D_{", String(n),"}"));
end;


__Bnaff_diagram:=function(n)
  local TheMat, ListEdge, i, eEdge;
  TheMat:=__ZerMat(n+1);
  ListEdge:=[[1,3],[2,3]];
  for i in [3..n-1]
  do
    Add(ListEdge, [i,i+1]);
  od;
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  TheMat[n][n+1]:=4;
  TheMat[n+1][n]:=4;
  return rec(type:="aff", eName:=Concatenation("tildeB", String(n)), TheMat:=TheMat);
end;


__Cnaff_diagram:=function(n)
  local TheMat, ListEdge, i, eEdge;
  TheMat:=__ZerMat(n+1);
  TheMat[1][2]:=4;
  TheMat[2][1]:=4;
  for i in [2..n-1]
  do
    Add(ListEdge, [i,i+1]);
  od;
  for eEdge in ListEdge
  do
    TheMat[eEdge[1]][eEdge[2]]:=3;
    TheMat[eEdge[2]][eEdge[1]]:=3;
  od;
  TheMat[n][n+1]:=4;
  TheMat[n+1][n]:=4;
  return rec(type:="aff", eName:=Concatenation("tildeC", String(n)), TheMat:=TheMat);
end;









ListIrreducibleFiniteFixedDimension:=function(nbpoint)
  local ListCases;
  ListCases:=[];
  Add(ListCases, __Anfin_diagram(nbpoint));
  if nbpoint>3 then
    Add(ListCases, __Dnfin_diagram(nbpoint));
  fi;
  if nbpoint=6 then
    Add(ListCases, __E6fin_diagram());
  fi;
  if nbpoint=7 then
    Add(ListCases, __E7fin_diagram());
  fi;
  if nbpoint=8 then
    Add(ListCases, __E8fin_diagram());
  fi;
  if nbpoint=4 then
    Add(ListCases, __F4fin_diagram());
  fi;
  if nbpoint>=2 then
    Add(ListCases, __Anaff_diagram(nbpoint-1));
  fi;
  if nbpoint>=5 then
    Add(ListCases, __Dnaff_diagram(nbpoint-1));
  fi;
  if nbpoint=7 then
    Add(ListCases, __E6aff_diagram());
  fi;
  if nbpoint=8 then
    Add(ListCases, __E7aff_diagram());
  fi;
  if nbpoint=9 then
    Add(ListCases, __E8aff_diagram());
  fi;
  return ListCases;
end;



RecognizeIrreducibleFiniteAffineCoxeterDynkinMatrix:=function(TheMat)
  local nbpoint, ListCases, eCase, eRepr, reply, ePerm;
  nbpoint:=Length(TheMat);
  ListCases:=ListIrreducibleFiniteFixedDimension(nbpoint);
  for eCase in ListCases
  do
    reply:=IsIsomorphicEdgeColoredGraph(TheMat, eCase.TheMat);
    if reply<>false then
      eRepr:=PermList(reply);
      if eCase.type="fin" then
        ePerm:=eRepr*eCase.ePerm*Inverse(eRepr);
      else
        ePerm:="irrelevant";
      fi;
      return rec(type:=eCase.type, 
eNameHumph:=eCase.eNameHumph, 
eNameLatexHumph:=eCase.eNameLatexHumph, 
eNameConway:=eCase.eNameConway, 
eNameLatexConway:=eCase.eNameLatexConway, 
ePerm:=ePerm);
    fi;
  od;
  Error("We did not find the matrix in the classification");
end;



GetInformation_FiniteAffineGroupDynkinDiagram:=function(ScalMat)
  local n, GRA, i, j, LConn, eList, ListNamesHumph, ListNamesLatexHumph, ListNamesConway, ListNamesLatexConway, eConn, RedMat, iVert, eVert, fVert, jVert, eReco, AllFinite, RetPerm;
  if TransposedMat(ScalMat)<>ScalMat then
    Error("The matrix is not symmetric, this won't work");
  fi;
  n:=Length(ScalMat);
  GRA:=NullGraph(Group(()), n);
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      if ScalMat[i][j]<>2 then
        AddEdgeOrbit(GRA, [i,j]);
        AddEdgeOrbit(GRA, [j,i]);
      fi;
    od;
  od;
  LConn:=ConnectedComponents(GRA);
  eList:=ListWithIdenticalEntries(n,0);
  ListNamesHumph:=[];
  ListNamesLatexHumph:=[];
  ListNamesConway:=[];
  ListNamesLatexConway:=[];
  AllFinite:=true;
  for eConn in LConn
  do
    RedMat:=List(ScalMat{eConn}, x->x{eConn});
    eReco:=RecognizeIrreducibleFiniteAffineCoxeterDynkinMatrix(RedMat);
    Add(ListNamesHumph, eReco.eNameHumph);
    Add(ListNamesLatexHumph, eReco.eNameLatexHumph);
    Add(ListNamesConway, eReco.eNameConway);
    Add(ListNamesLatexConway, eReco.eNameLatexConway);
    if eReco.type<>"fin" then
      AllFinite:=false;
    fi;
    if AllFinite=true then
      for iVert in [1..Length(eConn)]
      do
        eVert:=eConn[iVert];
        jVert:=OnPoints(iVert, eReco.ePerm);
        fVert:=eConn[jVert];
        eList[eVert]:=fVert;
      od;
    fi;
  od;
  if AllFinite=true then
    RetPerm:=PermList(eList);
  else
    RetPerm:="irrelevant";
  fi;
  return rec(ListNamesHumph:=ListNamesHumph,
ListNamesLatexHumph:=ListNamesLatexHumph,
ListNamesConway:=ListNamesConway,
ListNamesLatexConway:=ListNamesLatexConway,
ePerm:=RetPerm);
end;




LeechMatToCartanMat:=function(LeechDistMat)
  local nbV, CartanMat, i, j;
  nbV:=Length(LeechDistMat);
  CartanMat:=NullMat(nbV, nbV);
  for i in [1..nbV]
  do
    for j in [1..nbV]
    do
      if i=j then
        CartanMat[i][j]:=2;
      else
        if LeechDistMat[i][j]=4 then
          CartanMat[i][j]:=0;
        else
          CartanMat[i][j]:=-1;
        fi;
      fi;
    od;
  od;
  return CartanMat;
end;




LeechMatToCoxeterMat:=function(LeechDistMat)
  local nbV, CoxeterMat, i, j;
  nbV:=Length(LeechDistMat);
  CoxeterMat:=NullMat(nbV, nbV);
  for i in [1..nbV]
  do
    for j in [1..nbV]
    do
      if i=j then
        CoxeterMat[i][j]:=1;
      else
        if LeechDistMat[i][j]=4 then
          CoxeterMat[i][j]:=2;
        elif LeechDistMat[i][j]=6 then
          CoxeterMat[i][j]:=3;
        elif LeechDistMat[i][j]=8 then
          CoxeterMat[i][j]:="infty";
        else
          Error("Incorrect value");
        fi;
      fi;
    od;
  od;
  return CoxeterMat;
end;


FindOneFundamentalBasis:=function(ListRoot)
  local ListRootRed, nbVect, k, TestPositivityNegativityProperty, eSet, TheSystem, TheTest;
  ListRootRed:=ColumnReduction(ListRoot).EXT;
  nbVect:=Length(ListRootRed);
  k:=Length(ListRootRed[1]);
  TestPositivityNegativityProperty:=function(eListVect)
    local eVect, eSol, ListNeg, ListPos;
    if RankMat(eListVect)< k then
      return false;
    fi;
    for eVect in ListRootRed
    do
      eSol:=SolutionMat(eListVect, eVect);
      ListNeg:=Filtered(eSol, x->x<0);
      ListPos:=Filtered(eSol, x->x>0);
      if Length(ListNeg)>0 and Length(ListPos)>0 then
        return false;
      fi;
    od;
    return true;
  end;
  eSet:=InitialSub(nbVect, k);
  while(true)
  do
    TheSystem:=ListRootRed{eSet};
    TheTest:=TestPositivityNegativityProperty(TheSystem);
    if TheTest=true then
      return ListRoot{eSet};
    fi;
    eSet:=NextSubset(nbVect, eSet);
    if eSet=false then
      break;
    fi;
  od;
  return fail;
end;

DetermineCoxeterNatureFundamentalDomain:=function(GRPmatrFinite)
  local ListGens, TheDim, ListReflexion, ListRoot, eMat, DiffMatA, DiffMatB, NSPa, NSPb, TheNormal, TheCoxeterSubgroup, IsCoxeterTotal, TheBasis, k, EXTfundamental, GRPpermRoot, ListPermRoot, eGen, eList, GetRootPosition, Oroot, ListRootRepr, nbRoot;
  ListGens:=GeneratorsOfGroup(GRPmatrFinite);
  TheDim:=Length(ListGens[1]);
  ListReflexion:=[];
  ListRoot:=[];
  for eMat in GRPmatrFinite
  do
    DiffMatA:=eMat-IdentityMat(TheDim);
    DiffMatB:=eMat+IdentityMat(TheDim);
    NSPa:=NullspaceMat(DiffMatA);
    NSPb:=NullspaceMat(TransposedMat(DiffMatB));
    if Length(NSPa)=TheDim-1 then
      if Length(NSPb)<>1 then
        Error("Wrong space dimension");
      fi;
      TheNormal:=NSPb[1];
      Add(ListRoot, TheNormal);
      Add(ListRoot, -TheNormal);
      Add(ListReflexion, eMat);
    fi;
  od;
  nbRoot:=Length(ListRoot);
  TheCoxeterSubgroup:=PersoGroupMatrix(ListReflexion, TheDim);
  IsCoxeterTotal:=TheCoxeterSubgroup=GRPmatrFinite;
  GetRootPosition:=function(eRoot)
    local iRoot, fRoot, eSet, fSet, ListQuot, SetQuot, eVal;
    for iRoot in [1..Length(ListRoot)]
    do
      fRoot:=ListRoot[iRoot];
      eSet:=Filtered([1..TheDim], x->eRoot[x]<>0);
      fSet:=Filtered([1..TheDim], x->fRoot[x]<>0);
      if eSet=fSet then
        ListQuot:=List(eSet, x->eRoot[x]/fRoot[x]);
        SetQuot:=Set(ListQuot);
        if Length(SetQuot)=1 then
          eVal:=SetQuot[1];
          if eVal>0 then
            return iRoot;
          fi;
        fi;
      fi;
    od;
    Error("Error in RootFinding");
  end;
  ListPermRoot:=[];
  for eGen in GeneratorsOfGroup(TheCoxeterSubgroup)
  do
    eList:=List(ListRoot, x->GetRootPosition(eGen*x));
    if PermList(eList)=fail then
      Error("It is not a permutation");
    fi;
    Add(ListPermRoot, PermList(eList));
  od;
  GRPpermRoot:=Group(ListPermRoot);
  Oroot:=Orbits(GRPpermRoot, [1..nbRoot], OnPoints);
  ListRootRepr:=List(Oroot, x->ListRoot[x[1]]);
  if Length(ListRoot)=0 then
    TheBasis:="unset";
    EXTfundamental:="unset";
  else
    TheBasis:=FindOneFundamentalBasis(ListRoot);
    k:=Length(TheBasis);
    if k=TheDim then
      EXTfundamental:=DualDescription(TheBasis);
    else
      EXTfundamental:="unset";
    fi;
  fi;
  return rec(EXTfundamental:=EXTfundamental,
             ListRoot:=ListRoot,
             Oroot:=Oroot, 
             ListRootRepr:=ListRootRepr, 
             GRPpermRoot:=GRPpermRoot, 
             ListReflexion:=ListReflexion,
             TheCoxeterSubgroup:=TheCoxeterSubgroup,
             IsCoxeterTotal:=IsCoxeterTotal,
             TheBasis:=TheBasis);
end;
