% Huub has no remainder propagator. The remainder is what truncating division
% leaves, as Huub's own MiniZinc library states it.
%
% `div` reaches `int_div` and the product `int_times`, both of which Huub
% declares, so nothing here is rewritten back onto this predicate.

predicate fzn_int_mod(var int: a, var int: b, var int: c) = a = (a div b) * b + c;
