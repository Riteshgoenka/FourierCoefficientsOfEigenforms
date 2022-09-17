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

/*************************************************************************************
 * Check if \tau_k(p^2) = \pm q^a or \tau_k(p^4) = \pm q^a has a solution for p < 1000
 * ***********************************************************************************/
N := 10^3;
L := PrimesInInterval(3,100);

for k in {12, 16, 18, 20, 22, 26} do
	print "********";
	print k;
	print "********";
	M := CuspForms(1,k);
	B := Basis(M);
	f := B[1];
	P := PowerSeries(f,N);
	for p in PrimesInInterval(3,N) do
		cp 	:= Coefficient(P, p);
		cp2 := Abs(cp^2 - p^(k-1));
		cp4 := Abs(cp^4 - 3*p^(k-1)*cp^2 + p^(2*(k-1)));
		if IsPrimesPower(cp2, L) eq true or IsPrimesPower(cp4, L) eq true then
			print p;
		end if;
	end for;
end for;