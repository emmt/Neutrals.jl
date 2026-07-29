using Neutrals
using Test
using TypeUtils

"""
    x ≙ y

Return whether `x` and `y` have the same element types, the same axes, and the same values
(in the sense of `isequal`). It can be seen as a shortcut for:

    eltype(x) == eltype(y) && axes(x) == axes(y) && all(isequal, x, y)

"""
≙(x::Any, y::Any) = false
≙(x::T, y::T) where {T} = isequal(x, y)
function ≙(x::AbstractArray{T,N}, y::AbstractArray{T,N}) where {T,N}
    axes(x) == axes(y) || return false
    @inbounds for i in eachindex(x, y)
        isequal(x[i], y[i]) || return false
    end
    return true
end
