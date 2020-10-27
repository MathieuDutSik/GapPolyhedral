UNCOV_IsTiling:=function(EXTbig, ListEXT)
  local VolBig, ListVol, SumVol;
  VolBig:=VolumeComputationPolytope(EXTbig);
  ListVol:=List(ListEXT, VolumeComputationPolytope);
  SumVol:=Sum(ListVol);
  return SumVol=VolBig;
end;


UNCOV_RandomMethod:=function(EXTbig, ListEXT)
  local ListFAC, EXT, FAC, n, IsCorrect, eVect, eSum, eVal, eEXT, ePoint;
  ListFAC:=[];
  for EXT in ListEXT
  do
    FAC:=DualDescription(EXT);
    Add(ListFAC, FAC);
  od;
  n:=Length(EXTbig[1]);
  IsCorrect:=function(ePoint)
    local FAC, test;
    for FAC in ListFAC
    do
      test:=First(FAC, x->x*ePoint<0);
      if test=fail then
        return false;
      fi;
    od;
    return true;
  end;
  while(true)
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eSum:=0;
    for eEXT in EXTbig
    do
      eVal:=Random([1..20]);
      eSum:=eSum + eVal;
      eVect:=eVect + eVal*eEXT;
    od;
    ePoint:=eVect/eSum;
    if IsCorrect(ePoint)=true then
      return ePoint;
    fi;
  od;
end;
