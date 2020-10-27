# returns the list of vectors x in N^n such that
# x_1+2x_2+....+nx_n=S
#
# for the vector TheWeights=[y1, ...., y_n]
# returns the set of vectors v with
# y_1 x_1 + ..... + y_n x_n = S
ListOfPartitionsWeighted:=function(WeightVector,S)
  local q, eQuot, Solu, i, eSol, n, TheWeightsRed;
  n:=Length(WeightVector);
  if n=1 then
    eQuot:=S/WeightVector[1];
    if IsInt(eQuot)=true then
      return [[eQuot]];
    else
      return [];
    fi;
  else
    q:=QuoInt(S,WeightVector[n]);
    Solu:=[];
    TheWeightsRed:=WeightVector{[1..n-1]};
    for i in [0..q]
    do
      for eSol in ListOfPartitionsWeighted(TheWeightsRed,S-i*WeightVector[n])
      do
        Add(Solu, Concatenation(eSol, [i]));
      od;
    od;
    return Solu;
  fi;
end;

# if called with S=n, we get the partition number , whose first values are
# 1, 1, 2, 3, 5, 7, 11, 15, 22, ....
ListOfPartitions:=function(n,S)
  return ListOfPartitionsWeighted([1..n], S);
end;





GenerationRamanujanPartitions:=function(n)
  local ListCases, eSol, iPoint, eCase, iSize, iSet;
  ListCases:=[];
  for eSol in ListOfPartitions(n,n)
  do
    iPoint:=0;
    eCase:=[];
    for iSize in [1..Length(eSol)]
    do
      for iSet in [1..eSol[iSize]]
      do
        Add(eCase, [iPoint+1..iPoint+iSize]);
        iPoint:=iPoint+iSize;
      od;
    od;
    Add(ListCases, eCase);
  od;
  return ListCases;
end;

__OrbitsOnNelements:=function(N)
  local ListOrbitSizes, ePartition, NB, eSet;
  ListOrbitSizes:=[];
  for ePartition in GenerationRamanujanPartitions(N)
  do
    NB:=Factorial(N);
    for eSet in ePartition
    do
      NB:=NB/Factorial(Length(eSet));
    od;
    Add(ListOrbitSizes, NB);
  od;
  return Set(ListOrbitSizes);
end;


FullListPartition:=function(n)
  local ListPartition, ePartition, GRP, O;
  ListPartition:=[];
  GRP:=SymmetricGroup(n);
  for ePartition in GenerationRamanujanPartitions(n)
  do
    O:=Orbit(GRP, Set(ePartition), OnSetsSets);
    Append(ListPartition, O);
  od;
  return ListPartition;
end;





ListOrbits:=function(TheGroup, N, NB)
  local O, ListSizes, ListOrbit;
  O:=Orbits(TheGroup, [1..NB], OnPoints);
  ListSizes:=Set(List(O, x->Length(x)));
  ListOrbit:=List(O, x->rec(Orb:=x, siz:=Length(x)));
  if IsSubset(__OrbitsOnNelements(N), ListSizes)=false then
    return false;
  fi;
  return ListOrbit;
end;


General_FuncSearchSubSym:=function(EXT, GroupEXT)
  local TheDim, ListCandidates, iDim, SymGrp, ListIso, TheSubgroup, ListOrbit, eIso;
  TheDim:=Length(EXT[1])-1;
  ListCandidates:=[];
  for iDim in [3..TheDim]
  do
    SymGrp:=SymmetricGroup(iDim);
    ListIso:=IsomorphicSubgroups(GroupEXT, SymGrp);
    if Length(ListIso)>0 then
      for eIso in ListIso
      do
        TheSubgroup:=Image(eIso);
        ListOrbit:=ListOrbits(TheSubgroup, iDim, Length(EXT));
        if ListOrbit<>false then
          Add(ListCandidates, rec(Dim:=iDim, ListOrbit:=ListOrbit, eSubgroup:=TheSubgroup));
        fi;
      od;
    fi;
  od;
  return ListCandidates;
end;




OrbitSubPlanes:=function(EXT, GroupEXT)
  local rnk, LES, O, FuncInsert, ListOrbitPlanes, FuncCompletion, eCase, iRank, eNew, fCase;
  Print("|V|=", Length(EXT), " |G|=", Order(GroupEXT), "\n");
  rnk:=RankMat(EXT);
  LES:=[];
  O:=Orbits(GroupEXT, [1..Length(EXT)], OnPoints);
  FuncInsert:=function(eCase)
    local fCase;
    for fCase in LES
    do
      if RepresentativeAction(GroupEXT, eCase, fCase, OnSets)<>fail then
        return;
      fi;
    od;
    Add(LES, eCase);
  end;
  ListOrbitPlanes:=[List(O, x->[x[1]])];
  for iRank in [2..rnk-1]
  do
    LES:=[];
    FuncCompletion:=function(eCase)
      return Filtered([1..Length(EXT)], x->SolutionMat(EXT{eCase}, EXT[x])<>fail);
    end;
    for eCase in ListOrbitPlanes[iRank-1]
    do
      for eNew in Difference([1..Length(EXT)], eCase)
      do
        fCase:=FuncCompletion(Concatenation(eCase, [eNew]));
        FuncInsert(fCase);
      od;
    od;
    Add(ListOrbitPlanes, LES);
    Print("Find ", Length(LES), " planes of rank ", iRank, "\n");
  od;
  return ListOrbitPlanes;
end;




MaximalOrbitSubCube:=function(EXT, GroupEXT)
  local ListMaximalOrbit, O, LES, NewList, FuncCompletion, FuncInsert, eCase, IsMaximal, NewLadjVert, TotalList, eNew, TheDim;
  Print("|V|=", Length(EXT), " |G|=", Order(GroupEXT), "\n");
  O:=Orbits(GroupEXT, [1..Length(EXT)], OnPoints);
  LES:=List(O, x->rec(eVert:=x[1], LadjVert:=[], TotalList:=[x[1]]));
  ListMaximalOrbit:=[];
  while(true)
  do
    NewList:=[];
    TheDim:=Length(LES[1].LadjVert);
    Print("We have ", Length(LES), " orbits of cubes of dimension ", TheDim, "\n");
    FuncCompletion:=function(eVert, LadjVert)
      local ListTotal, eP, CandEXT, i, Pos;
      ListTotal:=[];
      for eP in BuildSet(Length(LadjVert), [0,1])
      do
        CandEXT:=EXT[eVert];
        for i in [1..Length(eP)]
        do
          if eP[i]=1 then
            CandEXT:=CandEXT+(EXT[LadjVert[i]]-EXT[eVert]);
          fi;
        od;
        Pos:=Position(EXT, CandEXT);
        if Pos=fail then
          return false;
        fi;
        Add(ListTotal, Pos);
      od;
      return Set(ListTotal);
    end;
    FuncInsert:=function(eVR)
      local fVR;
      for fVR in NewList
      do
        if RepresentativeAction(GroupEXT, eVR.TotalList, fVR.TotalList, OnSets)<>fail then
          return;
        fi;
      od;
      Add(NewList, eVR);
    end;
    for eCase in LES
    do
      IsMaximal:=true;
      for eNew in Difference([1..Length(EXT)], eCase.TotalList)
      do
        NewLadjVert:=ShallowCopy(eCase.LadjVert);
        Add(NewLadjVert, eNew);
        TotalList:=FuncCompletion(eCase.eVert, NewLadjVert);
        if TotalList<>false then
          FuncInsert(rec(eVert:=eCase.eVert, LadjVert:=NewLadjVert, TotalList:=TotalList));
          IsMaximal:=false;
        fi;
      od;
      if IsMaximal=true then
        Add(ListMaximalOrbit, eCase);
      fi;
    od;
    LES:=ShallowCopy(NewList);
    if Length(LES)=0 then
      break;
    fi;
  od;
  return ListMaximalOrbit;
end;


OrbitSubCrosspolytope:=function(EXT, GroupEXT, MaxDim)
  local FuncMap, LES, O, FuncInsert, eO, eVert, eStab, fO, ListOrbit, ListWork, ListMaximalOrbit, FuncCompletion, eCase, IsMaximal, eNew, fCase, TheDims, TheDim;
  Print("|V|=", Length(EXT), " |G|=", Order(GroupEXT), "\n");
  FuncMap:=function(eCase)
    local RET, eS;
    RET:=[];
    for eS in eCase
    do
      Append(RET, eS);
    od;
    return Set(RET);
  end;
  LES:=[];
  O:=Orbits(GroupEXT, [1..Length(EXT)], OnPoints);
  FuncInsert:=function(eCase)
    local fCase;
    for fCase in LES
    do
      if RepresentativeAction(GroupEXT, FuncMap(eCase), FuncMap(fCase), OnSets)<>fail then
        return;
      fi;
    od;
    Add(LES, eCase);
  end;
  for eO in O
  do
    eVert:=eO[1];
    eStab:=Stabilizer(GroupEXT, eVert, OnPoints);
    for fO in Orbits(eStab, Difference([1..Length(EXT)], [eVert]), OnPoints)
    do
      FuncInsert([[eVert, fO[1] ]]);
    od;
  od;
  ListOrbit:=ShallowCopy(LES);
  ListWork:=ShallowCopy(LES);
  ListMaximalOrbit:=[];
  while(true)
  do
    LES:=[];
    TheDim:=Length(ListWork[1]);
    Print("We have ", Length(ListWork), " orbits of cross polytopes of dimension ", TheDim, "\n");
    FuncCompletion:=function(eCase, eVert)
      local eSet, eMiddle, fCase, fEXT, Pos, LMAT;
      eSet:=eCase[1];
      eMiddle:=(EXT[eSet[1]]+EXT[eSet[2]])/2;
      fCase:=ShallowCopy(eCase);
      fEXT:=2*eMiddle-EXT[eVert];
      Pos:=Position(EXT, fEXT);
      if Pos=fail then
        return false;
      fi;
      Add(fCase, [eVert, Pos]);
      LMAT:=List(fCase, x->EXT[x[1]]-eMiddle);
      if RankMat(LMAT)<Length(LMAT) then
        return false;
      fi;
      return fCase;
    end;
    for eCase in ListWork
    do
      IsMaximal:=true;
      for eNew in Difference([1..Length(EXT)], FuncMap(eCase))
      do
        fCase:=FuncCompletion(eCase, eNew);
        if fCase<>false then
          FuncInsert(fCase);
          IsMaximal:=false;
        fi;
      od;
      if IsMaximal=true then
        Add(ListMaximalOrbit, eCase);
      fi;
    od;
    ListWork:=ShallowCopy(LES);
    if Length(ListWork)=0 then
      break;
    fi;
    Append(ListOrbit, LES);
    TheDims:=Set(List(ListWork, x->Length(x)));
    if Length(TheDims)>1 then
      Error("More than one dimension, this is not correct");
    fi;
    TheDim:=TheDims[1];
    if TheDim=MaxDim then
      break;
    fi;
  od;
  return rec(ListMaximalOrbit:=ListMaximalOrbit, ListOrbit:=ListOrbit);
end;




OrbitMaximalCentrallySymmetricSubpolytopes:=function(EXT, GroupEXT)
  local FuncMap, LES, O, FuncInsert, eO, eVert, eStab, fO, ListOrbit, ListWork, ListMaximalOrbit, FuncCompletion, eCase, IsMaximal, eNew, fCase, TheDim;
  Print("|V|=", Length(EXT), " |G|=", Order(GroupEXT), "\n");
  LES:=[];
  O:=Orbits(GroupEXT, [1..Length(EXT)], OnPoints);
  FuncInsert:=function(eCase)
    local fCase;
    for fCase in LES
    do
      if RepresentativeAction(GroupEXT, eCase, fCase, OnSets)<>fail then
        return;
      fi;
    od;
    Add(LES, eCase);
  end;
  for eO in O
  do
    eVert:=eO[1];
    eStab:=Stabilizer(GroupEXT, eVert, OnPoints);
    for fO in Orbits(eStab, Difference([1..Length(EXT)], [eVert]), OnPoints)
    do
      FuncInsert(  Set([eVert, fO[1]])  );
    od;
  od;
  ListOrbit:=ShallowCopy(LES);
  ListWork:=ShallowCopy(LES);
  ListMaximalOrbit:=[];
  while(true)
  do
    LES:=[];
    TheDim:=RankMat(EXT{ListWork[1]})-1;
    Print("We have ", Length(ListWork), " orbits of included centrally symmetric Delaunays of dimension ", TheDim, "\n");
    FuncCompletion:=function(eCase, eVert)
      local eMiddle, fEXT, Pos, PRV;
      eMiddle:=Sum(EXT{eCase})/Length(eCase);
      fEXT:=2*eMiddle-EXT[eVert];
      Pos:=Position(EXT, fEXT);
      if Pos=fail then
        return false;
      fi;
      PRV:=EXT{eCase};
      Add(PRV, EXT[eVert]);
      return Filtered([1..Length(EXT)], x->SolutionMat(PRV, EXT[x])<>fail);
    end;
    for eCase in ListWork
    do
      IsMaximal:=true;
      for eNew in Difference([1..Length(EXT)], eCase)
      do
        fCase:=FuncCompletion(eCase, eNew);
        if fCase<>false then
          FuncInsert(fCase);
          IsMaximal:=false;
        fi;
      od;
      if IsMaximal=true then
        Add(ListMaximalOrbit, eCase);
      fi;
    od;
    ListWork:=ShallowCopy(LES);
    Append(ListOrbit, LES);
    if Length(ListWork)=0 then
      break;
    fi;
  od;
  return ListMaximalOrbit;
end;






VertexSetJohnson:=function(n,s)
  local VertSet, TheRET, eVert, H;
  VertSet:=Filtered(BuildSet(n, [0,1]), x->Sum(x)=s);
  return List(VertSet, x->Concatenation([1], x));
end;


DistMatJohnson:=function(n,s)
  local VertSet, nbV, siz, DistMat, i, j, h;
  VertSet:=VertexSetJohnson(n,s);
  nbV:=Length(VertSet);
  siz:=Length(VertSet[1]);
  DistMat:=NullMat(nbV, nbV);
  for i in [1..nbV-1]
  do
    for j in [i+1..nbV]
    do
      h:=Length(Filtered([1..siz], x->VertSet[i][x]<>VertSet[j][x]));
      DistMat[i][j]:=h;
      DistMat[j][i]:=h;
    od;
  od;
  return DistMat;
end;


IsCorrectJohnsonPolytope:=function(n, s, EXT, IndexList)
  local VertexSet, TheDim, NSP, eZero, eNull, eSum, i;
  VertexSet:=VertexSetJohnson(n, s);
  TheDim:=Length(EXT[1]);
  NSP:=NullspaceMat(VertexSet);
  eZero:=ListWithIdenticalEntries(TheDim, 0);
  for eNull in NSP
  do
    eSum:=ShallowCopy(eZero);
    for i in [1..Length(VertexSet)]
    do
      eSum:=eSum+EXT[IndexList[i]]*eNull[i];
    od;
    if eSum<>eZero then
      return false;
    fi;
  od;
  return true;
end;


RaiseJohnsonPolytopes:=function(EXT, GroupEXT, nOrig, sOrig, sNew, WorkingList)
  local TheDim, VertexSetOrig, VertexSetNew, Lselect, ListPos, FirstNewVert, AffBas, ListPosFirstPartAffBas, eVert, eVertRed, Pos, TheNewList, FuncInsert, ListMaximal, IsMaximal, TheCompl, FuncCompletion, eNew, eCase;
  TheDim:=Length(EXT[1]);
  VertexSetOrig:=VertexSetJohnson(nOrig, sOrig);
  VertexSetNew:=VertexSetJohnson(nOrig+1, sNew);
  if sNew=sOrig then
    Lselect:=Filtered(VertexSetNew, x->x[1+nOrig+1]=0);
  else
    Lselect:=Filtered(VertexSetNew, x->x[1+nOrig+1]=1);
  fi;
  ListPos:=List(Lselect, x->Position(VertexSetNew, x));
  FirstNewVert:=Difference([1..Length(VertexSetNew)], ListPos)[1];
  AffBas:=CreateAffineBasis(Lselect);
  ListPosFirstPartAffBas:=[];
  for eVert in AffBas
  do
    eVertRed:=eVert{[1..nOrig+1]};
    Pos:=Position(VertexSetOrig, eVertRed);
    Add(ListPosFirstPartAffBas, Pos);
  od;
  Add(AffBas, VertexSetNew[FirstNewVert]);
  TheNewList:=[];
  FuncInsert:=function(eCase)
    local fCase;
    for fCase in TheNewList
    do
      if RepresentativeAction(GroupEXT, Set(fCase), Set(eCase), OnSets)<>fail then
        return;
      fi;
    od;
    if IsCorrectJohnsonPolytope(nOrig+1, sNew, EXT, eCase)=false then
      Error("We are inserting an inconsistent Johnson polytope");
    fi;
    Add(TheNewList, eCase);
  end;
  FuncCompletion:=function(eCase, eVert)
    local TheNewVertSet, eEXT, B, TheVert, i, Pos;
    B:=SolutionMat(EXT{eCase}, EXT[eVert]);
    if B<>fail then
      return false;
    fi;
    TheNewVertSet:=[];
    for eEXT in VertexSetNew
    do
      B:=SolutionMat(AffBas, eEXT);
      TheVert:=ListWithIdenticalEntries(TheDim, 0);
      for i in [1..nOrig]
      do
        TheVert:=TheVert+B[i]*EXT[eCase[ListPosFirstPartAffBas[i]]];
      od;
      TheVert:=TheVert+B[nOrig+1]*EXT[eVert];
      Pos:=Position(EXT, TheVert);
      if Pos=fail then
        return false;
      fi;
      Add(TheNewVertSet, Pos);
    od;
    return TheNewVertSet;
  end;
  ListMaximal:=[];
  for eCase in WorkingList
  do
    IsMaximal:=true;
    for eNew in Difference([1..Length(EXT)], Set(eCase))
    do
      TheCompl:=FuncCompletion(eCase, eNew);
      if TheCompl<>false then
        IsMaximal:=false;
        FuncInsert(TheCompl);
      fi;
    od;
    if IsMaximal=true then
      Add(ListMaximal, eCase);
    fi;
  od;
  return rec(ListMaximal:=ListMaximal, TheNewList:=TheNewList);
end;



CrossPolytope3_to_J42:=function(eCase)
  local VertexSet, NormedListVert, LST, LVert, eVert, Pos;
  VertexSet:=VertexSetJohnson(4, 2);
  NormedListVert:=[ [1, 1,1,0,0], [1, 1,0,1,0], [1, 1,0,0,1], 
                    [1, 0,1,1,0], [1, 0,1,0,1], [1, 0,0,1,1]];
  LST:=[eCase[1][1], eCase[2][1], eCase[3][1], 
        eCase[3][2], eCase[2][2], eCase[1][2]];
  LVert:=[];
  for eVert in VertexSet
  do
    Pos:=Position(NormedListVert, eVert);
    Add(LVert, LST[Pos]);
  od;
  return LVert;
end;



OrbitLiftingToCanonicalGroup:=function(n,s,ListOrbit)
  local NewListOrbit, VertexSet, DM, GRP, CanGroupGens, eGen, eList, CanGroup, eOrbit, eCos;
  VertexSet:=VertexSetJohnson(n,s);
  DM:=DistMatJohnson(n,s);
  GRP:=AutomorphismGroupEdgeColoredGraph(DM);
  CanGroupGens:=[];
  for eGen in GeneratorsOfGroup(SymmetricGroup([2..n+1]))
  do
    eList:=List(VertexSet, x->Position(VertexSet, Permuted(x, eGen)));
    Add(CanGroupGens, PermList(eList));
  od;
  CanGroup:=Group(CanGroupGens);
  NewListOrbit:=[];
  for eOrbit in ListOrbit
  do
    for eCos in RightCosets(GRP, CanGroup)
    do
      Add(NewListOrbit, Permuted(eOrbit, Representative(eCos)));
    od;    
  od;
  return NewListOrbit;
end;


# by interesting johnsons, we mean those which 
OrbitsInterestingJohnsons:=function(EXT, GroupEXT)
  local ListCrossLevel3, ListCross3, ListJ42, ListJ4, ListJohnson, n, IsFinished, NewSeriesS, WeDidIt, eC, test, TheList, s, eIndexList, VCE, LS, RealListMaximal, SeriesGeneration, ListGenerated, sOld, eCase;
  ListCrossLevel3:=OrbitSubCrosspolytope(EXT, GroupEXT, 3);
  ListCross3:=Filtered(ListCrossLevel3.ListOrbit, x->Length(x)=3);
  ListJ42:=List(ListCross3, x->CrossPolytope3_to_J42(x));
  for eIndexList in ListJ42
  do
    if IsCorrectJohnsonPolytope(4, 2, EXT, eIndexList)=false then
      Error("We made a mistake there");
    fi;
  od;
  ListJ4:=[rec(n:=4, s:=2, Orbit:=ListJ42)];
  Print("For n=4 s=2 |Orbit|=", Length(ListJ42), "\n");
  n:=4;
  ListJohnson:=[ListJ4];
  while(true)
  do
    IsFinished:=true;
    SeriesGeneration:=[];
    n:=n+1;
    for s in [2..n-2]
    do
      for eC in ListJohnson[n-4]
      do
        if eC.s=s or eC.s=s-1 then
          test:=1;
        else
          test:=0;
        fi;
        if test=1 then
          TheList:=RaiseJohnsonPolytopes(EXT, GroupEXT, n-1, eC.s, s, OrbitLiftingToCanonicalGroup(n-1, eC.s, eC.Orbit));
          Add(SeriesGeneration, rec(n:=n, s:=s, sOld:=eC.s, Maxi:=TheList.ListMaximal, Orbit:=TheList.TheNewList));
          if Length(TheList.TheNewList)>0 then
            IsFinished:=false;
          fi;
        fi;
      od;
    od;
    # doing sanity checks
    NewSeriesS:=[];
    for s in [2..n-2]
    do
      LS:=Filtered(SeriesGeneration, x->x.s=s);
      if Length(LS)=1 then
        ListGenerated:=LS[1].Orbit;
      else
        ListGenerated:=LS[1].Orbit;
        for eCase in LS[2].Orbit
        do
          VCE:=Filtered(ListGenerated, x->RepresentativeAction(GroupEXT, Set(x), Set(eCase), OnSets)<>fail);
          if Length(VCE)<>1 then
            Error("We have an inconsistency in OrbitIntersectionJohnson");
          fi;
        od;
      fi;
      Add(NewSeriesS, rec(n:=n, s:=s, Orbit:=ListGenerated));
      Print("n=", n, "   s=", s, "   |nbGen|=", Length(ListGenerated), "\n");
    od;
    Add(ListJohnson, NewSeriesS);
    Print("\n");
    # DeterminingMaximalElements
    for sOld in [2..n-3]
    do
      LS:=Filtered(SeriesGeneration, x->x.sOld=sOld);
      RealListMaximal:=Intersection(Set(LS[1].Maxi), Set(LS[2].Maxi));
      ListJohnson[n-4][sOld-1].ListMaximal:=RealListMaximal;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  return ListJohnson;
end;







HalfCubeVertices:=function(n)
  return List(Filtered(BuildSet(n, [0,1]), x->Sum(x) mod 2=0), x->Concatenation([1], x));
end;


SemiCubeEnumeration:=function(EXT, GroupEXT, ListJohnsonN2, n)
  local TheDim, VertexSetHalfCube, TheNewList, FuncInsert, VertexSetJohnsonN2, AffBas, eVect, Pos, ListPosAffBas, ZeroVect, FuncCompletion, eCase, eNew, TheCompl;
  TheDim:=Length(EXT[1]);
  VertexSetHalfCube:=HalfCubeVertices(n);
  TheNewList:=[];
  FuncInsert:=function(eCase)
    local fCase;
    for fCase in TheNewList
    do
      if RepresentativeAction(GroupEXT, Set(fCase), Set(eCase), OnSets)<>fail then
        return;
      fi;
    od;
    Add(TheNewList, eCase);
  end;
  VertexSetJohnsonN2:=VertexSetJohnson(n, 2);
  AffBas:=CreateAffineBasis(VertexSetJohnsonN2);
  ListPosAffBas:=[];
  for eVect in AffBas
  do
    Pos:=Position(VertexSetJohnsonN2, eVect);
    Add(ListPosAffBas, Pos);
  od;
  ZeroVect:=ListWithIdenticalEntries(n+1,0);
  ZeroVect[1]:=1;
  Add(AffBas, ZeroVect);
  FuncCompletion:=function(eCase, eVert)
    local TheNewVertSet, eEXT, B, TheVert, Pos, i;
    B:=SolutionMat(EXT{eCase}, EXT[eVert]);
    if B<>fail then
      return false;
    fi;
    TheNewVertSet:=[];
    for eEXT in VertexSetHalfCube
    do
      B:=SolutionMat(AffBas, eEXT);
      TheVert:=ListWithIdenticalEntries(TheDim, 0);
      for i in [1..n]
      do
        TheVert:=TheVert+B[i]*EXT[eCase[ListPosAffBas[i]]];
      od;
      TheVert:=TheVert+B[n+1]*EXT[eVert];
      Pos:=Position(EXT, TheVert);
      if Pos=fail then
        return false;
      fi;
      Add(TheNewVertSet, Pos);
    od;
    return TheNewVertSet;
  end;
  for eCase in ListJohnsonN2
  do
    for eNew in Difference([1..Length(EXT)], Set(eCase))
    do
      TheCompl:=FuncCompletion(eCase, eNew);
      if TheCompl<>false then
        FuncInsert(TheCompl);
      fi;
    od;
  od;
  return TheNewList;
end;


OrbitSemiCubes:=function(EXT, GroupEXT)
  local ListCrossLevel3, ListCross3, ListJ4, ListJohnsonN2, n, IsFinished, NewSeriesS, TheList, len, ListOrbitSemiCube, ListGen;
  Print("Computing first the J(N,2) polytopes\n");
  ListCrossLevel3:=OrbitSubCrosspolytope(EXT, GroupEXT, 3);
  ListCross3:=Filtered(ListCrossLevel3.ListOrbit, x->Length(x)=3);
  ListJohnsonN2:=[List(ListCross3, x->CrossPolytope3_to_J42(x))];
  n:=4;
  while(true)
  do
    Print("|Orbit J(", n, ",2)|=", Length(ListJohnsonN2[n-3]), "\n");
    IsFinished:=true;
    NewSeriesS:=[];
    n:=n+1;
    TheList:=RaiseJohnsonPolytopes(EXT, GroupEXT, n-1, 2, 2, OrbitLiftingToCanonicalGroup(n-1, 2, ListJohnsonN2[n-4]));
    if Length(TheList.TheNewList)>0 then
      IsFinished:=false;
    fi;
    Add(ListJohnsonN2, TheList.TheNewList);
    if IsFinished=true then
      break;
    fi;
  od;
  len:=Length(ListJohnsonN2);
  ListOrbitSemiCube:=[];
  for n in [4..len+3]
  do
    ListGen:=SemiCubeEnumeration(EXT, GroupEXT, ListJohnsonN2[n-3], n);
    Print("|Orbit 1/2H(", n, ")|=", Length(ListGen), "\n");
    Add(ListOrbitSemiCube, ListGen);
  od;
  return ListOrbitSemiCube;
end;











FindScaledEmbedding:=function(DM1, SymGrp1, DMbig, SymGrpBig)
  local Oext, ListPotential, eOrb, iter, NewListPotential, eSol, ListPosDist1, EVS1, EVS2, fVert, ListPosDist2, NewSol, NewOrig, NewDest, eCase, ListOfPossibleMapping, NbrExtensions, pos, TheMin, test, nb, MatC, iF, ListCases, eFL, FuncCanonicalize, IsEquivalentEmbedding, FuncInsert;
  Oext:=Orbits(SymGrpBig, [1..Length(DMbig)], OnPoints);
  ListPotential:=List(Oext, x->[[1], [x[1]]]);
  for iter in [2..Length(DM1)]
  do
    Print("We have ", Length(ListPotential), " possibilities\n");
    IsEquivalentEmbedding:=function(eSol1, eSol2)
      local g, NewIM, LEP, g2, g3, VSol;
      g:=RepresentativeAction(SymGrpBig, Set(eSol1[2]), Set(eSol2[2]), OnSets);
      if g=fail then
        return false;
      fi;
      NewIM:=OnTuples(eSol1[2], g);
      LEP:=List(NewIM, x->Position(eSol2[2], x));
      g2:=PermList(LEP);
      # we have    Permuted(NewIM, g2) = eSol2[2]
      VSol:=Permuted(eSol1[1], g2);
      g3:=OnTuplesRepresentativeAction(SymGrp1, VSol, eSol2[1]);
      if g3=fail then
        return false;
      fi;
      return true;
    end;
    NewListPotential:=[];
    FuncInsert:=function(eSol)
      local fSol;
      for fSol in NewListPotential
      do
        if IsEquivalentEmbedding(eSol, fSol)=true then
          return;
        fi;
      od;
      Add(NewListPotential, eSol);
    end;
#    FuncCanonicalize:=function(eSol)
#      local eRepr, g, NewIM, g2, LEP, NewSol, fRepr;
#      eRepr:=Minimum(Orbit(SymGrpBig, Set(eSol[2]), OnSets));
#      g:=RepresentativeAction(SymGrpBig, Set(eSol[2]), eRepr, OnSets);
#      NewIM:=OnTuples(eSol[2], g);
#      LEP:=List(NewIM, x->Position(eRepr, x));
#      g2:=PermList(LEP);
#      NewSol:=[Permuted(eSol[1], g2), Permuted(NewIM, g2)];
#      fRepr:=CanonicalizationOnTuplesAction(NewSol[1], SymGrp1);
#      return [fRepr, NewSol[2]];
#    end;
    for eSol in ListPotential
    do
      EVS1:=Difference([1..Length(DM1)], eSol[1]);
      ListPosDist1:=List(EVS1, x->DM1[x]{eSol[1]});
      EVS2:=Difference([1..Length(DMbig)], eSol[2]);
      ListPosDist2:=List(EVS2, x->DMbig[x]{eSol[2]});
      NbrExtensions:=[];
      ListOfPossibleMapping:=[];
      for eFL in ListPosDist1
      do
        ListCases:=Filtered([1..Length(ListPosDist2)], x->ListPosDist2[x]=eFL);
        Add(ListOfPossibleMapping, ListCases);
        Add(NbrExtensions, Length(ListCases));
      od;
      test:=true;
      for eCase in Set(ListPosDist1)
      do
        nb:=Length(Filtered(ListPosDist1, x->x=eCase));
        pos:=Position(ListPosDist1, eCase);
        if NbrExtensions[pos]<nb then
          test:=false;
        fi;
      od;
      TheMin:=Minimum(NbrExtensions);
      if TheMin>0 and test=true then
        pos:=Position(NbrExtensions, TheMin);
        for eCase in ListOfPossibleMapping[pos]
        do
          NewOrig:=ShallowCopy(eSol[1]);
          Add(NewOrig, EVS1[pos]);
          NewDest:=ShallowCopy(eSol[2]);
          Add(NewDest, EVS2[eCase]);
          NewSol:=[NewOrig, NewDest];
          FuncInsert(NewSol);
        od;
      fi;
    od;
    ListPotential:=ShallowCopy(NewListPotential);
  od;
  return ListPotential;
end;





FindIsometricEmbedding:=function(DM1, SymGrp1, DM2, SymGrp2)
  local n1, ListDist1, i, n2, ListDist2, SmallDist1, ListPossibleScaling, eDist, eScal, ScalDist, eEmbed, ListEmbedding, eSol, ECR;
  n1:=Length(DM1);
  ListDist1:=[];
  for i in [1..n1]
  do
    ListDist1:=Union(ListDist1, Set(DM1[i]));
  od;
  Print("ListDist = ", ListDist1, "\n");
  n2:=Length(DM2);
  ListDist2:=[];
  for i in [1..n2]
  do
    ListDist2:=Union(ListDist2, Set(DM2[i]));
  od;
  Print("ListDist = ", ListDist2, "\n");
  SmallDist1:=Minimum(Difference(ListDist1, [0]));
  ListPossibleScaling:=[];
  for eDist in ListDist2
  do
    if eDist<>0 then
      eScal:=eDist/SmallDist1;
      ScalDist:=eScal*ListDist1;
      if IsSubset(ListDist2, ScalDist)=true then
        Add(ListPossibleScaling, eScal);
      fi;
    fi;
  od;
  ListEmbedding:=[];
  for eScal in ListPossibleScaling
  do
    Print("eScal=", eScal, "\n");
    for eEmbed in FindScaledEmbedding(eScal*DM1, SymGrp1, DM2, SymGrp2)
    do
      ECR:=Set(eEmbed[2]);
      eSol:=Minimum(Orbit(SymGrp2, ECR, OnSets));
      AddSet(ListEmbedding, eSol);
    od;
  od;
  return ListEmbedding;
end;


JohnsonPolytope:=function(n,k)
  local EXT, eSet, eVect, GRP, ListGens, eGen, eList, PermGRP;
  EXT:=[];
  for eSet in Combinations([1..n], k)
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect{eSet}:=ListWithIdenticalEntries(k,1);
    Add(EXT, eVect);
  od;
  GRP:=SymmetricGroup(n);
  ListGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=List(EXT, x->Position(EXT, Permuted(x, eGen)));
    Add(ListGens, PermList(eList));
  od;
  PermGRP:=Group(ListGens);
  return rec(EXT:=EXT, GRP:=PermGRP);
end;
