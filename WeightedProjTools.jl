using Pkg
Pkg.add(["Combinatorics", "Memoization", "Primes"])

import Base: getproperty, propertynames # for dynamic fields

using Memoization

function dimrec(a, d) # find not too restrictive hint typing
    @memoize function helper(i, remaining)
        if i == length(a) + 1
            return remaining == 0 ? 1 : 0
        end
        total = 0
        for k in 0:div(remaining, a[i])
            total += helper(i + 1, remaining - k * a[i])
        end
        return total
    end

    return helper(1, d)
end


function unique_bi_sol(a::Int, s::Int, d::Int; verbose=false) #could get rid of verbose
    g, x, y = gcdx(a, s)

    @assert g == 1 "a = $a and s = $s must be coprime (gcd = 1), but got gcd = $g"
    #if d % g != 0 #in our case always works exits because a and s are coprime so g=1
    #    error("No integer solution exists because gcd(a, s) does not divide d.")
    #end

    # Scale the particular solution (x, y) by d / g
    x *= d #div(d, g)
    y *= d #div(d, g)

    # General solution:
    # b = x + t * (s ÷ g)
    # c = y - t * (a ÷ g)
    step = s #div(s, g)

    # Adjust t to get b in [0, s)
    t = fld(-x, step)  # floor division to shift b into range
    b = x + t * step

    # If b is still not in range (rare corner case), adjust once more
    if b < 0
        b += step
    elseif b >= s
        b -= step
    end

    if !(0 <= b < s)
        error("No valid b found in range [0, $s)") #shouldn't happen ever normally
    end

    if verbose
        c = div(d - a * b, s)
        println("$d = $b * $a + $c * $s = $(a*b + s*c)")
    end

    return b
end


function reduce_arr(func::Function, arr::AbstractVector)
    output = []
    for i in 1:length(arr)
        arrhat = vcat(arr[1:i-1], arr[i+1:end])
        push!(output, reduce(func, arrhat))
    end
    return output
    # alternative: [func(arr[1:i-1]..., arr[i+1:end]...) for i in 1:length(arr)]
end
 

using Combinatorics

function very_ample_bound(weights::Vector{Int})
    r = length(weights) - 1
    if r == 0
        return -weights[1]
    end
    temp_sum = 0.0
    for nu in 2:(r + 1)
        for subset in combinations(weights, nu)
            temp_sum += reduce(lcm, subset) / binomial(r - 1, nu - 2)
        end
    end
    return -sum(weights) + temp_sum / r
end


# slower so don't actually use
@memoize function very_ample_bound_recursive(weights::Vector{Int})
    r = length(weights) - 1
    if r == 0
        return -weights[1]
    end
    total = 0.0
    for i in 1:length(weights)
        w_hat = vcat(weights[1:i-1], weights[i+1:end])
        total += very_ample_bound_recursive(w_hat)
    end
    m = reduce(lcm, weights)
    return (total + m) / r
end


struct Weights
    weights::Vector{Int}
    reduced_weights::Vector{Int}
    wellformed_weights::Vector{Int} 
    gcd::Int   #same name as function but it seems julia doesn't mess it up so okay
    sub_gcd::Vector{Int} # comment to agree with paper notation
    sub_lcm_of_sub_gcd::Vector{Int}
    lcm_of_sub_gcd::Int
    lcm::Int

    function Weights(weights::Vector{Int})
        sorted_weights = sort(weights)
        gcd_val = reduce(gcd, sorted_weights) #here gcd is the built in function
        reduced = [div(w, gcd_val) for w in sorted_weights]
        sub_gcds = reduce_arr(gcd, reduced)
        sub_lcms = reduce_arr(lcm, sub_gcds)
        wellformed = [div(r, l) for (r, l) in zip(reduced, sub_lcms)]
        lcm_sub_gcd = reduce(lcm, sub_gcds)
        lcm_val = reduce(lcm, sorted_weights)
        new(sorted_weights, reduced, wellformed, gcd_val, sub_gcds, sub_lcms, lcm_sub_gcd, lcm_val)
    end
end

function getproperty(w::Weights, name::Symbol) # getproperty ie . method is already defined in Julia, but we override it. 
    if name === :is_reduced
        return w.weights == w.reduced_weights
    elseif name === :is_wellformed
        return w.weights == w.wellformed_weights
    else
        return getfield(w, name) # this is the default behavior of getproperty
    end
end

# Show properties in REPL
function propertynames(w::Weights; private=false)
    return (:weights, :reduced_weights, :wellformed_weights, :gcd,
            :sub_gcd, :sub_lcm_of_sub_gcd, :lcm_of_sub_gcd, :lcm,
            :is_reduced, :is_wellformed)
end

struct TwistedSheaf
    W::Weights
    degree::Int
    reduced_degree::Union{Int, Nothing}
    wellformed_degree::Union{Float64, Nothing}
    unique_bs::Union{Vector{Int}, Nothing}

    function TwistedSheaf(W::Weights, degree::Int)
        if is_deg_reducible(W, degree)
            reduced_deg, wellformed_deg, unique_bs = compute_wellformed_degree(W, degree)
        else
            reduced_deg = nothing
            wellformed_deg = nothing
            unique_bs = nothing
        end
        new(W, degree, reduced_deg, wellformed_deg, unique_bs)
    end
end


function getproperty(O::TwistedSheaf, name::Symbol) # getproperty ie . method is already defined in Julia, but we override it. 
    if name === :is_deg_reducible 
        return is_deg_reducible(O.W, O.degree)
    elseif name === :is_ample
        return is_ample(O)
    elseif name === :is_very_ample
        return is_very_ample(O)
    else
        return getfield(O, name) # this is the default behavior of getproperty
    end
end

# Show properties in REPL
function propertynames(O::TwistedSheaf; private=false)
    return (:W, :degree, :reduced_degree, :wellformed_degree, :unique_bs,
            :is_deg_reducible, is_ample, :is_very_ample)
end


function compute_wellformed_degree(W::Weights, degree::Int) 
    reduced_degree = Int(round(degree / W.gcd))
    unique_bs = [unique_bi_sol(ai, si, reduced_degree) for (ai, si) in zip(W.reduced_weights, W.sub_gcd)]
    dot_product = sum(b * a for (b, a) in zip(unique_bs, W.reduced_weights))
    wellformed_degree = (reduced_degree - dot_product) / W.lcm_of_sub_gcd
    return reduced_degree, wellformed_degree, unique_bs
end

function is_deg_reducible(W::Weights, degree::Int)::Bool
    temp = degree / W.gcd
    precision = 1e-10
    return abs(temp - round(temp)) < precision
end

function is_ample(O::TwistedSheaf)::Bool
    return O.degree == O.W.lcm # or should I be checking for wellformed_degree and lcm of wellformed_weights?
end

function is_very_ample(O::TwistedSheaf)::Union{Bool, Nothing}
    if O.wellformed_degree !== nothing
        m = lcm(O.W.wellformed_weights...)
        if O.wellformed_degree % m == 0
            G = very_ample_bound(O.W.wellformed_weights)
            return O.wellformed_degree > 0 && O.wellformed_degree >= G
        else
            return false
        end
    else
        return nothing
    end
end


struct LinearSystem
    sheaf::TwistedSheaf
    dimension::Int

    function LinearSystem(W::Weights, degree::Int)
        sheaf = TwistedSheaf(W, degree)
        if sheaf.wellformed_degree !== nothing
            dim = dimrec(W.wellformed_weights, sheaf.wellformed_degree) - 1
        else
            dim = dimrec(W.weights, degree) - 1
        end
        new(sheaf, dim)
    end
end

"""
function getproperty(L::LinearSystem, name::Symbol)
    if name in (:W, :degree, :wellformed_degree)
        return getproperty(L.sheaf, name)
    else
        return getfield(L, name)
    end
end

function propertynames(L::LinearSystem; private=false)
    return (:sheaf, :dimension, :W, :degree, :reduced_degree, :wellformed_degree,
            :is_deg_reducible, :is_ample, :is_very_ample)
end
"""

struct WeightedProjectiveSpace
    W::Weights
    m::Int
    G::Float64
    embedding_dimension::Int
    embedding_degree::Int
    embedding_linear_system::LinearSystem

    function WeightedProjectiveSpace(W::Weights)
        m_val = reduce(lcm, W.wellformed_weights)
        G_val = very_ample_bound(W.wellformed_weights)
        n = G_val / m_val < 0 ? 1 : ceil(Int, G_val / m_val)
        deg_mn = n * m_val
        linsys = LinearSystem(Weights(W.wellformed_weights), deg_mn)
        N = linsys.dimension
        new(W, m_val, G_val, N, deg_mn, linsys)
    end
end
