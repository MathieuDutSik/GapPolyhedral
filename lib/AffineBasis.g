IsLocallyOKPartialAffineBasis:=function(ThePartial, TheEXT)
  local eVert, B, eVal;
  for eVert in TheEXT
  do
    B:=SolutionMat(ThePartial, eVert);
    if B<>fail then
      for eVal in B
      do
        if IsInt(eVal)=false then
          return false;
        fi;
      od;
    fi;
  od;
  return true;
end;


FindAffineBasisExtension:=function(OldAffineBasis, EXT)
  local eVert, PROV;
  for eVert in EXT
  do
    PROV:=ShallowCopy(OldAffineBasis);
    Add(PROV, eVert);
    if RankMat(PROV)=Length(PROV) then
      if IsLocallyOKPartialAffineBasis(PROV, EXT)=true then
        return PROV;
      fi;
    fi;
  od;
  return false;
end;


Kernel_ExtendToCompleteAffineBasis:=function(EXT, StartingPoint)
  local AffBasis, iRank, TheReply, PersoRank;
  PersoRank:=function(EXT)
    if Length(EXT)=0 then
      return 0;
    fi;
    return RankMat(EXT);
  end;
  AffBasis:=ShallowCopy(StartingPoint);
  for iRank in [PersoRank(AffBasis)+1..PersoRank(EXT)]
  do
    TheReply:=FindAffineBasisExtension(AffBasis, EXT);
    if TheReply=false then
#      Print("afBasis=", AffBasis, "\n");
#      Print("Error, no affine basis found\n");
      return false;
    fi;
    AffBasis:=ShallowCopy(TheReply);
  od;
  return AffBasis;
end;

ExtendToCompleteAffineBasis:=function(EXT, StartingPoint)
  local TheAffBas, len, GRP, nbIter, ePerm, EXTperm;
  TheAffBas:=Kernel_ExtendToCompleteAffineBasis(EXT, StartingPoint);
  if TheAffBas<>false then
    return TheAffBas;
  fi;
  len:=Length(EXT);
  GRP:=SymmetricGroup(len);
  nbIter:=0;
  while(true)
  do
    if nbIter> 10000 then
      Print("Maybe there is no affine basis after all");
      return false;
    fi;
    ePerm:=Random(GRP);
    EXTperm:=Permuted(EXT, ePerm);
    TheAffBas:=Kernel_ExtendToCompleteAffineBasis(EXTperm, StartingPoint);
    if TheAffBas<>false then
      return TheAffBas;
    fi;
    nbIter:=nbIter+1;
  od;
end;

CreateAffineBasis:=function(EXT)
  local ePerm, test, nbRun;
  nbRun:=0;
  while(true)
  do
    ePerm:=Random(SymmetricGroup(Length(EXT)));
    test:=ExtendToCompleteAffineBasis(Permuted(EXT, ePerm), []);
    nbRun:=nbRun+1;
    if test<>false then
      return test;
    fi;
    if nbRun>1000 then
      Print("Failure to get affine basis after 1000 runs");
      return false;
    fi;
  od;
end;

CreateAffineBasisNumberTry:=function(EXT, MaxNbTry)
  local ePerm, test, nbRun;
  nbRun:=0;
  while(true)
  do
    ePerm:=Random(SymmetricGroup(Length(EXT)));
    test:=ExtendToCompleteAffineBasis(Permuted(EXT, ePerm), []);
    nbRun:=nbRun+1;
    if test<>false then
      return test;
    fi;
    if nbRun>MaxNbTry then
      return false;
    fi;
  od;
end;







#
# Polytope is the list of vertices
# Graph is the skeleton of the polytope
# Group is the symmetry group of the polytope (usually equal to the 
# symmetry group of the skeleton graph)
FindAllOrbitAffineBasis:=function(Polytope, Group)
  local Dimension, FuncLinear;
  Dimension:=RankMat(Polytope);
  FuncLinear:=function(eCand)
    local Matr, ePos, iVert, Solu, eV;
    Matr:=[];
    for ePos in eCand
    do
      Add(Matr, Polytope[ePos]);
    od;
    if RankMat(Matr)<Length(eCand) then
      return false;
    fi;
    for iVert in Difference([1..Length(Polytope)], eCand)
    do
      Solu:=SolutionMat(Matr, Polytope[iVert]);
      if Solu<>fail then
        for eV in Solu
        do
          if IsInt(eV)=false then
            return false;
          fi;
        od;
      fi;
    od;
    return true;
  end;
  return FindOrbitSubGraphs(Length(Polytope), Group, FuncLinear, Dimension);
end;

#
# Find all orbits of independent points in the polytope
# (Their determinant can be any non-negative integer a priori)
FindAllOrbitIndependent:=function(Polytope, Group)
  local Dimension, FuncLinear;
  Dimension:=RankMat(Polytope);
  FuncLinear:=function(eCand)
    local Matr, ePos, iVert, Solu, eV;
    Matr:=[];
    for ePos in eCand
    do
      Add(Matr, Polytope[ePos]);
    od;
    if RankMat(Matr)<Length(eCand) then
      return false;
    fi;
    return true;
  end;
  return FindOrbitSubGraphs(Length(Polytope), Group, FuncLinear, Dimension);
end;






#
#
# AffineBasis is a sequence of numbers refering to elements of the polytope
TestAffineBasis:=function(EXT, AffineBasis)
  local Matr, eEXT, B;
  Matr:=EXT{AffineBasis};
  for eEXT in EXT
  do
    B:=SolutionMat(Matr, eEXT);
    if B=fail then
      return false;
    fi;
    if IsIntegralVector(B)=false then
      return false;
    fi;
  od;
  return true;
end;

