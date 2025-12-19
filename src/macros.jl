"""
     Neutrals.@dispatch_on_value sym expr

Expand to code dispatching expression `expr` depending on the numerical value bound to
symbol `sym` at run-time. Only a few specific values are considered: `0`, `1`, and `-1`,
possibly with units. This is to generate code optimized for specific values that can be
represented by neutral numbers.

For example:

```julia
function xpby!(dst::AbstractArray, x::AbstractArray, β::Number, y::AbstractArray)
    @assert axes(dst) == axes(x) == axes(y)
    @dispatch_on_value β unsafe_xpby!(dst, x, β, y)
    return dst
end
function unsafe_xpby!(dst::AbstractArray, x::AbstractArray, β::Number, y::AbstractArray)
    @inbounds @simd for i in eachindex(dst, x, y)
        dst[i] = x[i] + β*y[i]
    end
    nothing
end
```

where the `@dispatch_on_value ...` statement expands to (with comments removed):

```julia
if !Neutrals.is_static_number(β) && Base.iszero(β)
    unsafe_xpby!(dst, α, x, Neutrals.Neutral{0}()*TypeUtils.units_of(β), y)
elseif !Neutrals.is_static_number(β) && β == Base.oneunit(β)
    unsafe_xpby!(dst, α, x, Neutrals.Neutral{1}()*TypeUtils.units_of(β), y)
elseif !Neutrals.is_static_number(β) && TypeUtils.is_signed(β) && β == -Base.oneunit(β)
    unsafe_xpby!(dst, α, x, Neutrals.Neutral{-1}()*TypeUtils.units_of(β), y)
else
    unsafe_xpby!(dst, α, x, β, y)
end
```

This can be checked with `@macroexpand`:

```julia
@macroexpand Neutrals.@dispatch_on_value β unsafe_xpby!(dst, x, β, y)
```

"""
macro dispatch_on_value(sym::Union{Symbol,QuoteNode}, expr::Expr)
    esc(:(if !Neutrals.is_static_number($sym) && Base.isequal($sym, Base.zero($sym))
              $(recode(expr, sym => :(Neutrals.Neutral{0}()*TypeUtils.units_of($sym))))
          elseif !Neutrals.is_static_number($sym) && Base.isequal($sym, Base.oneunit($sym))
              $(recode(expr, sym => :(Neutrals.Neutral{1}()*TypeUtils.units_of($sym))))
          elseif !Neutrals.is_static_number($sym) && TypeUtils.is_signed($sym) && Base.isequal($sym, -Base.oneunit($sym))
              $(recode(expr, sym => :(Neutrals.Neutral{-1}()*TypeUtils.units_of($sym))))
          else
              $expr
          end))
end

"""
    Neutrals.recode(ex, a => b, ...) -> ex′

Return expression `ex` with all symbols or macros named `a` replaced by `b`. If any of `a`
or `b` is a string, it is first converted into a symbol. There may be any number of
replacement rules all specified by pairs. If there are more than one rule, the first
(leftmost) one is fully applied to `ex`, then the second one is fully applied to the
resulting expression, and so on.

"""
recode(ex::Expr, pairs::Pair...) = recode!(deepcopy(ex), pairs...)

"""
    Neutrals.recode!(ex, a => b, ...) -> ex

Return expression `ex` with all symbols or macros named `a` replaced by `b`. This is the
same as [`Neutrals,recode`](@ref) except that the operation may be performed in-place (i.e.
modifying the content of `ex`).

"""
recode!(ex::Expr, pair::Pair, pairs::Pair...) = recode!(recode!(ex, pair), pairs...)
function recode!(ex::Expr, (a, b)::Pair)
    a = _symbolic(a)
    b = _symbolic(b)
    for i in eachindex(ex.args)
        if ex.args[i] isa Expr
            recode!(ex.args[i], a => b)
        elseif isequal(ex.args[i], a)
            ex.args[i] = b
        end
    end
    return ex
end
_symbolic(x::AbstractString) = Symbol(x)
_symbolic(x::Any) = x
