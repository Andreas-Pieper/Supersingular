declare type ssEllCurvEndStr;
declare attributes ssEllCurvEndStr: E, B, indep, indepB, FB, A, Tan, basis, basisB;

/* This file defines a new data type of a supersingular elliptic curve with an endomorphism structure. Here

E is a supersingular elliptic curve defined over GF(p) with base field containing GF(p^2).
B is a quaternion algebra isomorphic to End^0(E)
indep is a tuple of 4 Z-linearly independent elements of End(E) represented as isogenies E -> E.
indepB is a tuple of 4 Z-linearly independent elements of B, such that the map indep[i] -> indepB[i] defines an isomorphism of Q-algebras End^0(E) -> B
FB is the element in B corresponding to the geometric p-Frobenius.
A is the change of basis matrix from indepB to the internal basis of B
Tan describes the action on the tangent space of the elements in indep
basis is a Z-basis of End(E) represented as isogenies E -> E
basisB the image of basis under the above isomorphism End^0(E) -> B
 */

intrinsic Print(X::ssEllCurvEndStr)
{Print X}
printf "Endomorphism structure on the supersingular elliptic curve %o", X`E;
end intrinsic;


intrinsic ssEllipticCurveEndStr(E::CrvEll, B::AlgQuat, indep::SeqEnum, indepB::SeqEnum, FB::AlgQuatElt)-> ssEllCurvEndStr
{Creates an elliptic curve with the given endomorphism structure.}
require forall{phi: phi in indep | ISA(Type(phi), Map)}:"Tuple entries in 3rd argument are not all isogenies";
require forall{r: r in indepB | Parent(r) eq B}: "Tuple entries in 4th argument are not all elements of B";
Str:=New(ssEllCurvEndStr);
Str`E:=E;
Str`B:=B;
Str`indep:=indep;
Str`indepB:=indepB;
Str`FB:=FB;
Str`A:=Matrix([Coordinates(a): a in indepB]);
k:=BaseField(E);
R<eps>:=quo<PolynomialRing(k)|$.1^2>;
/*The formula in the next line uses that the k[eps]/(eps^2)-valued point (-eps,1,0) generates the tangent space at 0 of E. 
Caution: If the rational functions in indep are not defined at 0, there is a division by zero.*/
Str`Tan:=[-MonomialCoefficient(Evaluate(DefiningEquations(indep[i])[1],[-eps,1,0]),eps)/MonomialCoefficient(Evaluate(DefiningEquations(indep[i])[2],[-eps,1,0]),1): i in [1..4]];
return Str;
end intrinsic;

intrinsic Endomorphism(Str::ssEllCurvEndStr,r::AlgQuatElt) -> Map
{Returns the endomorphism corresponding to the element r in B}
require Parent(r) eq Str`B: "2nd argument not an element of B";
K<x,y>:=FunctionField(Str`E);
E_:=BaseChange(Str`E,K);
b:=Coordinates(Str`B,r);
x:=Solution(Str`A,Matrix([b]));
return asMap(Str`E, &+[Integers()![x[1][i]] * asPoint(Str`E, Str`indep[i], E_): i in [1..4]]);
end intrinsic;


intrinsic asPoint(E1::CrvEll, phi::Map, E_::CrvEll) -> PtEll
{Interprets a map E->E as a point E(K(E))}
K:=BaseField(E_);
require K eq FunctionField(E1): "3rd argument not defined over the function field of 1st argument";
require E_ eq BaseChange(E1,K): "3rd argument not base change of 1st argument";
x:=K.1;
y:=K.2;
P:=E_![Evaluate(DefiningPolynomials(phi)[1],[x,y,1]),Evaluate(DefiningPolynomials(phi)[2],[x,y,1]),Evaluate(DefiningPolynomials(phi)[3],[x,y,1])];
return P;
end intrinsic;

intrinsic asMap(E1::CrvEll, P::PtEll) -> Map
{Returns the map E-> corresponding to a point in E(K(E))}
return map<E1-> E1 | Coordinates(P)>;
end intrinsic;


intrinsic ActionOnTangentSpace(Str::ssEllCurvEndStr, r::AlgQuatElt) -> FinFldElt
{returns the scalar alpha such that the endomorphism corresponding to r acts by multiplication by alpha on the tangent space.}
b:=Coordinates(Str`B,r);
x:=Solution(Str`A,Matrix([b]));
return &+[IntegerRing()!(x[1][i])*Str`Tan[i]: i in [1..4] ];

end intrinsic;
