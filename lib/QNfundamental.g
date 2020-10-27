FileTestlp2_QN:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"testlp2_QN");
FileRedcheck_QN:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"redcheck_QN");
FilelpcddcleanerQN:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"lpcddcleanerQN");

# we use here the presentation of the field Q(\sqrt(N)) as
# a set of pairs [p,q] corresponding to p+q\sqrt(N)

# It takes as argument an element of the form
# x + y Sqrt(Nval) and returns [x,y]
QN_GetExpression:=function(Nval, eX)
  local a, b, hRet;
  if IsRat(eX)=true then
    return [eX, 0];
  else
    hRet:=RationalizedMat([[eX]])/2;
    a:=hRet[1][1];
    b:=(eX - a)/Sqrt(Nval);
    if IsRat(b)=false then
      Error("Inconsistency in QN_GetExpression");
    fi;
    return [a,b];
  fi;
end;


#return true if eX>0
QN_IsPositive:=function(Nval, eX)
  local p, q, h, eElt;
  eElt:=QN_GetExpression(Nval, eX);
  p:=eElt[1];
  q:=eElt[2];
  if p=0 and q=0 then
    return false;
  fi;
  if p>=0 and q>=0 then
    return true;
  fi;
  if p<=0 and q<=0 then
    return false;
  fi;
  h:=p*p-Nval*q*q;
  if h*p>0 then
    return true;
  else
    return false;
  fi;
end;

QN_IsNonNegative:=function(Nval, eX)
  if eX=0 then
    return true;
  fi;
  return QN_IsPositive(Nval, eX);
end;



QN_IsElement:=function(Nval, eX)
  local a, b, hRet;
  if IsRat(eX)=true then
    return true;
  else
    hRet:=RationalizedMat([[eX]])/2;
    a:=hRet[1][1];
    b:=(eX - a)/Sqrt(Nval);
    if IsRat(b)=false then
      return false;
    fi;
    return true;
  fi;
end;

QN_IsVector:=function(Nval, eVect)
  local eX;
  for eX in eVect
  do
    if QN_IsElement(Nval, eX)=false then
      return false;
    fi;
  od;
  return true;
end;

QN_IsMatrix:=function(Nval, eMat)
  local eVect;
  for eVect in eMat
  do
    if QN_IsVector(Nval, eVect)=false then
      return false;
    fi;
  od;
  return true;
end;

QN_IsMatrixFamily:=function(Nval, ListMat)
  local eMat;
  for eMat in ListMat
  do
    if QN_IsMatrix(Nval, eMat)=false then
      return false;
    fi;
  od;
  return true;
end;





QN_WriteVector:=function(Nval, output, eEXT)
  local eVal, ePair;
  for eVal in eEXT
  do
    ePair:=QN_GetExpression(Nval, eVal);
    AppendTo(output, " ", ePair[1], " ", ePair[2]);
  od;
  AppendTo(output, "\n");
end;


QN_GetFunctionSet:=function(Nval)
  local IsPositive, IsStrictlyPositive, IsNegative, IsStrictlyNegative;
  IsPositive:=function(x)
    if x=0 then
      return true;
    fi;
    return IsStrictlyPositive(x);
  end;
  IsStrictlyPositive:=function(x)
    return QN_IsPositive(Nval, x);
  end;
  IsNegative:=function(x)
    return IsPositive(-x);
  end;
  IsStrictlyNegative:=function(x)
    return IsStrictlyPositive(-x);
  end;
  return rec(IsPositive:=IsPositive, IsStrictlyPositive:=IsStrictlyPositive, IsNegative:=IsNegative, IsStrictlyNegative:=IsStrictlyNegative);
end;
