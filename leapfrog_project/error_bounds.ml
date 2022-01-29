(* A function that computes the upper bound for 
 * round off error in "n" steps of leapfrog 
 * integration *)


let rec delta_x  n = match n with
        | 0 -> 0.0  
        | _ -> (1.0 -. 0.5 *. 0.3125**2.) *. (delta_x (n-1)) +. 0.03125 *. (delta_v (n-1)) +. 1.25*.10.**(-7.)

        and delta_v m = match m with 
        | 0 -> 0.  
        | _ -> (1.0 -. 0.5 *. (0.03125)**2.) *. (delta_v (m-1)) +.  0.5 *. 0.03125 *. (2.0 -. 0.5 *. 0.03125**2.) *. delta_x (m-1) +. 6.723*.10.**(-8.);;


print_float (delta_x 16);; 
