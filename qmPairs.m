/**********************************************
 * Function to check if n = p^a for some a >= 0
 * ********************************************/
IsPrimePower := function(n, p)
	assert IsPrime(p);
	while n gt 1 do
		if IsDivisibleBy(n, p) eq true then
			n := n div p;
		else
			return false;
		end if;
	end while;
	return true;
end function;

/*******************************************************
 * Function to check if n = p^a for some p \in P, a >= 0
 * *****************************************************/
IsPrimesPower := function(n, P)
	for p in P do
		if IsPrimePower(n, p) eq true then
			return true;
		end if;
	end for;
	return false;
end function;

/*************************************************************
 * We solve the equation \Psi_m(X,Y) = \pm q^a for (q,m) pairs
 * **********************************************************/

load "ThueMahlerSolver.m";

Pairs := [[13,7],[23,11],[29,7],[37,19],[41,7],[43,7],[43,11],[47,23],[53,13],[59,29],[61,31],[67,11],[67,17],[71,7],[73,37],[79,13],[83,7],[83,41],[89,11],[97,7]];

for pair in Pairs do
	q := pair[1];
	m := pair[2];

	for a in [-1, 1] do
		print "*******************************";
		print q, m, a;
		print "*******************************";

		ZXY<X,Y>:=PolynomialRing(Integers(),2);

		seq:=[1,X];
		for n in [2..m] do
			Append(~seq,X*seq[n]-Y*seq[n-1]);
		end for;


		deq:=[];
		for i in [1..m] do
			if IsOdd(i) then
				g:=ZXY!0;
				f := seq[i];
				mons:=Monomials(f);
				assert &and[ IsEven(Degree(m,X)) : m in mons];
				g:=&+[ MonomialCoefficient(f,m)*X^(Degree(m,X) div 2)*Y^Degree(m,Y)   : m in mons];
				assert Evaluate(g,X,X^2) eq f;
				Append(~deq,g);
			end if;
		end for;

		Zx<x>:=PolynomialRing(Integers());

		f:=Evaluate(seq[m],[1,x]);
		clist:=Coefficients(f);

		Sols := solveThueMahler(clist,a,[q]);

		for sol in Sols do
			tau := sol[1];
			pk := sol[2];
			if IsDivisibleBy(tau,2) and pk ge 3 and IsPrimesPower(pk,PrimesInInterval(3,pk)) and not(IsDivisibleBy(pk,q)) then
				print tau, pk, sol[3];
			end if;
		end for;
	end for;
end for;
