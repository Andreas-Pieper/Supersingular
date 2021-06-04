Attach("ssEllCurvEndStr.m");

padicVal:=function(r,p)
Zp:=pAdicRing(p);
return Valuation(Zp!Norm(r));
end function;

g_H:=function(Str, R, KExE, gnum,gden, alpha)
E:=Str`E;
p:=Characteristic(KExE);
y1 := KExE.1;
y2 := KExE.2;
x1 := KExE.3;
x2 := KExE.4;
zcal:=R.1;
Laurent<z>:=LaurentSeriesRing(KExE,p+2);
E_:=BaseChange(E,Laurent);
P1:=E_![x1,y1,1];
P2:=E_![x2,y2,1];
Log, P:=FormalLog(E:Precision:=p+2);
Exp:=Reverse(Log);
z1:=Evaluate(Exp, alpha[1]*zcal);
z2:=Evaluate(Exp, alpha[2]*zcal);
Sum1:=P1+E_!P;
Sum2:=P2+E_!P;
eval1:=[Evaluate(Coordinates(Sum1)[i], z1): i in [1..3]];
eval2:=[Evaluate(Coordinates(Sum2)[i], z2): i in [1..3]];
return [Evaluate(gnum,[eval1[2]/eval1[3],eval2[2]/eval2[3],eval1[1]/eval1[3],eval2[1]/eval2[3],1]),Evaluate(gden,[eval1[2]/eval1[3],eval2[2]/eval2[3],eval1[1]/eval1[3],eval2[1]/eval2[3],1])];
end function;



intrinsic MoretBailly(Str::ssEllCurvEndStr, f::AlgMatElt, f1::AlgMatElt,f2::AlgMatElt,f_1::AlgMatElt,f_2::AlgMatElt)
{Computes the family constructed by L. Moret-Bailly}
T:=Time();
E:=Str`E;
a1:=Coefficients(E)[1];
a2:=Coefficients(E)[2];
a3:=Coefficients(E)[3];
a4:=Coefficients(E)[4];
a6:=Coefficients(E)[5];
B:=Str`B;
indepB:=Str`indepB;
indep:=Str`indep;
FB:=Str`FB;
k:=BaseField(E);
p:=Characteristic(k);
K:=FunctionField(E);
E_:=BaseChange(E,K);
//Construct the Kummer surface
A3<x1,x2,t>:=AffineSpace(k,3);
Kum:=Scheme(A3,[t^2-(x1^3+a2*x1^2+a4*x1+a6)*(x2^3+a2*x2^2+a4*x2+a6) ]);
KumProj:=ProjectiveClosure(Kum);
P3:=Ambient(KumProj);
//Construct an affine patch of ExE
A4<y1,y2,x1,x2>:=AffineSpace(k,4);
ExEAff:=Scheme(A4, [y1^2-(x1^3+a2*x1^2+a4*x1+a6), y2^2-(x2^3+a2*x2^2+a4*x2+a6)]);
AExE:=CoordinateRing(ExEAff);
KExE:=FieldOfFractions(AExE);
ExEAffProj:=ProjectiveClosure(ExEAff);
P4:=Ambient(ExEAffProj);
psi:=map<ExEAff-> Kum | [x1,x2,y1*y2]>;
/* The kernels of f1,f2,f_1,f_2 is used to define maps E-> Kum with image C1, C2, C_1, C_2
Notice that Magma computes the left kernel ker(A)={x|xA=0}
 */
v1:=Basis(Kernel(f1))[1];
v2:=Basis(Kernel(f2))[1];
v_1:=Basis(Kernel(f_1))[1];
v_2:=Basis(Kernel(f_2))[1];
A:=Matrix([Coordinates(a): a in indepB]);
Y1:=Matrix([Coordinates(B,v1[i]): i in [1,2]]) ;
Y2:=Matrix([Coordinates(B,v2[i]): i in [1,2]]) ;
Y_1:=Matrix([Coordinates(B,v_1[i]): i in [1,2]]) ;
Y_2:=Matrix([Coordinates(B,v_2[i]): i in [1,2]]) ;
D1:=Lcm(Flat([[Denominator((Solution(A,Y1)) [i,j]): i in [1..2] ]: j in [1..4] ]));
val1:=Min(padicVal(D1*v1[1],p),padicVal(D1*v1[2],p));
if val1 mod 2 eq 0 then
  v1:=D1*1/(IntegerRing()!(p^(val1/2)))*v1;
else
 v1:=FB*D1*1/(IntegerRing()!(p^((val1+1)/2)))*v1;
end if;
D2:=Lcm(Flat([[Denominator((Solution(A,Y2)) [i,j]): i in [1..2] ]: j in [1..4] ]));
val2:=Min(padicVal(D2*v2[1],p),padicVal(D2*v2[2],p));
if val2 mod 2 eq 0 then
     v2:=D2*1/(IntegerRing()!(p^(val2/2)))*v2;
else
     v2:=FB*D2*1/(IntegerRing()!(p^((val2+1)/2)))*v2;
end if;
D_1:=Lcm(Flat([[Denominator((Solution(A,Y_1)) [i,j]): i in [1..2] ]: j in [1..4] ]));
val_1:=Min(padicVal(D_1*v_1[1],p),padicVal(D_1*v_1[2],p));
if val_1 mod 2 eq 0 then
     v_1:=D_1*1/(IntegerRing()!(p^(val_1/2)))*v_1;
else
     v_1:=FB*D_1*1/(IntegerRing()!(p^((val_1+1)/2)))*v_1;
end if;
D_2:=Lcm(Flat([[Denominator((Solution(A,Y_2)) [i,j]): i in [1..2] ]: j in [1..4] ]));
val_2:=Min(padicVal(D_2*v_2[1],p),padicVal(D_2*v_2[2],p));
if val_2 mod 2 eq 0 then
     v_2:=D_2*1/(IntegerRing()!(p^(val_2/2)))*v_2;
else
     v_2:=FB*D_2*1/(IntegerRing()!(p^((val_2+1)/2)))*v_2;
end if;
Trans:=Translate(Str,f,f1,f2,f_1,f_2);
phi11:=asMap(E,asPoint(E,Endomorphism(Str, Conjugate(v1[1])),E_)+E_!Trans[1]);
phi12:=asMap(E,asPoint(E,Endomorphism(Str, Conjugate(v1[2])),E_)+E_!Trans[1]);
phi21:=asMap(E,asPoint(E,Endomorphism(Str, Conjugate(v2[1])),E_)+E_!Trans[2]);
phi22:=asMap(E,asPoint(E,Endomorphism(Str, Conjugate(v2[2])),E_)+E_!Trans[2]);
phi_11:=asMap(E,asPoint(E,Endomorphism(Str, Conjugate(v_1[1])),E_)+E_!Trans[3]);
phi_12:=asMap(E,asPoint(E,Endomorphism(Str, Conjugate(v_1[2])),E_)+E_!Trans[3]);
phi_21:=asMap(E,asPoint(E,Endomorphism(Str, Conjugate(v_2[1])),E_)+E_!Trans[4]);
phi_22:=asMap(E,asPoint(E,Endomorphism(Str, Conjugate(v_2[2])),E_)+E_!Trans[4]);
phi1:=map<E-> Kum |  [DefiningPolynomials(phi11)[1]/DefiningPolynomials(phi11)[3] , DefiningPolynomials(phi12)[1]/DefiningPolynomials(phi12)[3], (DefiningPolynomials(phi11)[2]/DefiningPolynomials(phi11)[3]) * (DefiningPolynomials(phi12)[2]/DefiningPolynomials(phi12)[3])]>;
C1:=Image(phi1);
phi2:=map<E-> Kum |  [DefiningPolynomials(phi21)[1]/DefiningPolynomials(phi21)[3] , DefiningPolynomials(phi22)[1]/DefiningPolynomials(phi22)[3], (DefiningPolynomials(phi21)[2]/DefiningPolynomials(phi21)[3]) * (DefiningPolynomials(phi22)[2]/DefiningPolynomials(phi22)[3])]>;
C2:=Image(phi2);
phi_1:=map<E-> Kum |  [DefiningPolynomials(phi_11)[1]/DefiningPolynomials(phi_11)[3] , DefiningPolynomials(phi_12)[1]/DefiningPolynomials(phi_12)[3], (DefiningPolynomials(phi_11)[2]/DefiningPolynomials(phi_11)[3]) * (DefiningPolynomials(phi_12)[2]/DefiningPolynomials(phi_12)[3])]>;
C_1:=Image(phi_1);
phi_2:=map<E-> Kum |  [DefiningPolynomials(phi_21)[1]/DefiningPolynomials(phi_21)[3] , DefiningPolynomials(phi_22)[1]/DefiningPolynomials(phi_22)[3], (DefiningPolynomials(phi_21)[2]/DefiningPolynomials(phi_21)[3]) * (DefiningPolynomials(phi_22)[2]/DefiningPolynomials(phi_22)[3])]>;
C_2:=Image(phi_2);
//Define the divisors D, D_ on the image of ExE ---> P^4
D:=ProjectiveClosure(Pullback(psi,Scheme(Kum,DefiningEquations(Union(C1, C2)))));
D_:=ProjectiveClosure(Pullback(psi, Scheme(Kum,DefiningEquations(Union(C_1, C_2)))));
//D, D_ are rationally equivalent. Compute a rational function g with (g)=D-D_
rr_seq,G, Sl := IneffectiveRiemannRochBasis(ExEAffProj,ideal<CoordinateRing(P4)|DefiningEquations(D)>,ideal<CoordinateRing(P4)|DefiningEquations(D_)>);
R<z>:=quo<PolynomialRing(KExE)| $.1^p>;
S<eps,eps_>:=quo<PolynomialRing(KExE,2)| $.1^2, $.2^2>;
alpha:=[ActionOnTangentSpace(Str, Conjugate(v1[i])): i in [1..2]];
alpha_:=[ActionOnTangentSpace(Str, Conjugate(v_1[i])): i in [1..2]];
y1 := KExE.1;
y2 := KExE.2;
x1 := KExE.3;
x2 := KExE.4;
gHout:=g_H(Str, R, KExE, rr_seq[1], G, alpha);
//Multiply the coefficients with G
gH:= (gHout[1]*(gHout[2])^(p-1)*Evaluate(G,[KExE.1,KExE.2,KExE.3,KExE.4,1]))/(gHout[2])^p;
gHcoeff:=Coefficients(gH);
/*ks<s>:=RationalFunctionField(k);
Kumks:=BaseChange(Kum,ks);
AKumks:=CoordinateRing(Kumks);
f:=hom<KExE->AKumks|AKumks.3,1,AKumks.1,AKumks.2>;
gHMat:=HorizontalJoin(Matrix([[f(c): c in gHcoeff]]),ZeroMatrix(AKumks,1,p+1-#gHcoeff));
eva:=Matrix([Flat([[Factorial(2*i)*(-(AKumks!s)/2)^i/Factorial(i),0]:i in [0..((p-1)/2)]  ])]);
gtildaG:=(gHMat*Transpose(eva))[1,1];
C:=Difference(Scheme(Kumks,[gtildaG]), Scheme(Kumks,[ f(Evaluate(G,[KExE.1,KExE.2,KExE.3,KExE.4,1]))]));
P:=Curve(C)!Coordinates( (Points(Intersection(C1, Scheme(Kum,[(Kum.1^3+a2*Kum.1^2+a4*Kum.1+a6),(Kum.2^3+a2*Kum.2^2+a4*Kum.2+a6),Kum.3]))) sdiff Points(Intersection(C2, Scheme(Kum,[(Kum.1^3+a2*Kum.1^2+a4*Kum.1+a6),(Kum.2^3+a2*Kum.2^2+a4*Kum.2+a6),Kum.3]))))[1]);
print Basis(Divisor(P));*/
n:=4;
ExEAffpn:=BaseChange(ExEAff,GF(p^n));
A:=CoordinateRing(ExEAffpn);
f:=hom<KExE->A|A.1,A.2,A.3,A.4>;
gHMat:=HorizontalJoin(Matrix([[f(c): c in gHcoeff]]),ZeroMatrix(A,1,p+1-#gHcoeff));
for param in GF(p^n) do
	    if param^(p^2) ne param then
	    print param;
	         eva:=Matrix([Flat([[Factorial(2*i)*(-(A!param)/2)^i/Factorial(i),0]:i in [0..((p-1)/2)]  ])]);
                 gtildaG:=(gHMat*Transpose(eva))[1,1];
                 C:=Difference(Scheme(ExEAffpn,[gtildaG]), Scheme(ExEAffpn,[ Evaluate(G,[A.1,A.2,A.3,A.4,1])]));
                 b, Cnorm, f:=IsHyperelliptic(Curve(C));
                 b, Codd:=HasOddDegreeModel(Cnorm);
                 if b then
		    print Codd;
		 else
		   print Cnorm;
                 end if;
break;
            end if;
end for;
end intrinsic;

intrinsic Translate(Str::ssEllCurvEndStr, f::AlgMatElt, f1::AlgMatElt,f2::AlgMatElt,f_1::AlgMatElt,f_2::AlgMatElt)->SeqEnum
{This function computes two points P, P_ in E^2[2] such that t_P^* D is rationally equivalent to t_P_^*D_ and both divisors have no components at infinity.}
E:=Str`E;
a1:=Coefficients(E)[1];
a2:=Coefficients(E)[2];
a3:=Coefficients(E)[3];
a4:=Coefficients(E)[4];
a6:=Coefficients(E)[5];
B:=Str`B;
indepB:=Str`indepB;
indep:=Str`indep;
k:=BaseField(E);
//Construct the 2-Torsion points on E:
R<x>:=PolynomialRing(k);
f:=(x^3+a2*x^2+a4*x+a6);
Roots:=RootsInSplittingField(f);
l:=Parent(Roots[1][1]);
El:=BaseChange(E,l);
Two00:=Zero(El);
Two01:=El![Roots[1][1],0,1];
Two10:=El![Roots[2][1],0,1];
Two11:=El![Roots[3][1],0,1];
//Compute the action of the Endomorphism ring on E[2]:
RepTwo:=[ZeroMatrix(GF(2),2,2): i in [1..4]];
for i:=1 to 4 do
       Im01:=indep[i](Two01);
       Im10:=indep[i](Two10);
       if  Coordinates(Im10) eq  Coordinates(Two01) then
            RepTwo[i][1]:=Vector([GF(2)|0,1]);
       elif  Coordinates(Im10) eq  Coordinates(Two10) then
            RepTwo[i][1]:=Vector([GF(2)|1,0]);
       elif  Coordinates(Im10) eq  Coordinates(Two11) then
            RepTwo[i][1]:=Vector([GF(2)|1,1]);
       end if;
       if Coordinates(Im01) eq  Coordinates(Two01) then
            RepTwo[i][2]:=Vector([GF(2)|0,1]);
       elif Coordinates(Im01) eq  Coordinates(Two10) then
            RepTwo[i][2]:=Vector([GF(2)|1,0]);
       elif Coordinates(Im01) eq  Coordinates(Two11) then
            RepTwo[i][2]:=Vector([GF(2)|1,1]);
       end if;				     
end for;
RepTwo:=[Transpose(A): A in RepTwo];
f1Z:=Solution(Str`A,BlockMatrix(2,1, [Matrix([Coordinates(f1[i,j]): i in [1..2]]): j in [1..2]]));
f2Z:=Solution(Str`A,BlockMatrix(2,1, [Matrix([Coordinates(f2[i,j]): i in [1..2]]): j in [1..2]]));
f_1Z:=Solution(Str`A,BlockMatrix(2,1, [Matrix([Coordinates(f_1[i,j]): i in [1..2]]): j in [1..2]]));
f_2Z:=Solution(Str`A,BlockMatrix(2,1, [Matrix([Coordinates(f_2[i,j]): i in [1..2]]): j in [1..2]]));
f1Z2:=BlockMatrix(2,2, [&+[RepTwo[i]*f1Z[j,i]: i in [1..4] ]: j in [1..4]]);
f2Z2:=BlockMatrix(2,2, [&+[RepTwo[i]*f2Z[j,i]: i in [1..4] ]: j in [1..4]]);
f_1Z2:=BlockMatrix(2,2, [&+[RepTwo[i]*f_1Z[j,i]: i in [1..4] ]: j in [1..4]]);
f_2Z2:=BlockMatrix(2,2, [&+[RepTwo[i]*f_2Z[j,i]: i in [1..4] ]: j in [1..4]]);
Q:=ZeroMatrix(GF(2),4,4);
Q_:=ZeroMatrix(GF(2),4,4);
for i:=1 to 4 do
	Q[i,i]:=boolGF2(Matrix(Transpose(f1Z2)[i]) eq 0)+boolGF2(Matrix(Transpose(f2Z2)[i]) eq 0) ;
	Q_[i,i]:=boolGF2(Matrix(Transpose(f_1Z2)[i]) eq 0)+boolGF2(Matrix(Transpose(f_2Z2)[i]) eq 0) ;
end for;
for i:=1 to 4 do
	 for j:=i+1 to 4 do
		  Q[i,j]:=Q[i,i]+Q[j,j]+boolGF2(Matrix(Transpose(f1Z2)[i]+Transpose(f1Z2)[j]) eq 0)+boolGF2(Matrix(Transpose(f2Z2)[i]+Transpose(f2Z2)[j]) eq 0) ;
		  Q_[i,j]:=Q_[i,i]+Q_[j,j]+boolGF2(Matrix(Transpose(f_1Z2)[i]+Transpose(f_1Z2)[j]) eq 0)+boolGF2(Matrix(Transpose(f_2Z2)[i]+Transpose(f_2Z2)[j]) eq 0) ;
         end for;
end for;
d:=Matrix([[Q[i,i]+Q_[i,i]: i in [1..4]]]);
v:=Solution(Q+Transpose(Q),d);
v1:=v*Matrix(GF(2),[[0,1],[1,1],[0,0],[0,0]]);
v1_:=v*Matrix(GF(2),[[1,1],[1,0],[0,0],[0,0]]);
v2:=v*Matrix(GF(2),[[0,0],[0,0],[0,1],[1,1]]);
v2_:=v*Matrix(GF(2),[[0,0],[0,0],[1,1],[1,0]]);
if v1 eq 0 then
     P1:=Two01;
     v1_:= Matrix(GF(2),[[0,1]]);
elif v1 eq Matrix(GF(2),[[0,1]]) then
     P1:=Two01;
elif v1 eq Matrix(GF(2),[[1,0]]) then
     P1:=Two10;
elif v1 eq Matrix(GF(2),[[1,1]]) then
     P1:=Two11;
end if;
if v2 eq 0 then
     P2:=Two01;
     v2_:= Matrix(GF(2),[[0,1]]);
elif v2 eq Matrix(GF(2),[[0,1]]) then
     P2:=Two01;
elif v2 eq Matrix(GF(2),[[1,0]]) then
     P2:=Two10;
elif v2 eq Matrix(GF(2),[[1,1]]) then
     P2:=Two11;
end if;
if v1_ eq 0 then
     P1_:=Two00;
     print "something went wrong here";
elif v1_ eq Matrix(GF(2),[[0,1]]) then
     P1_:=Two01;
elif v1_ eq Matrix(GF(2),[[1,0]]) then
     P1_:=Two10;
elif v1_ eq Matrix(GF(2),[[1,1]]) then
     P1_:=Two11;
end if;
if v2_ eq 0 then
     P2_:=Two00;
     print "something went wrong here";
elif v2_ eq Matrix(GF(2),[[0,1]]) then
     P2_:=Two01;
elif v2_ eq Matrix(GF(2),[[1,0]]) then
     P2_:=Two10;
elif v2_ eq Matrix(GF(2),[[1,1]]) then
     P2_:=Two11;
end if;
return [P1,P2,P1_,P2_];
end intrinsic;

intrinsic boolGF2(bool::BoolElt) -> FldFinElt
{Converts a boolean variable to GF(2)}
if bool then
     return GF(2)!1;
else
     return GF(2)!0;
end if;
end intrinsic;



