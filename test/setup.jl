using Test

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

# For abstract floats, the sign is not always consistent with 0 and NaN depending on whether
# the code is inlined or not. FIXME Is this a bug in Julia?
sloppy_isequal(x::T, y::T) where {T<:AbstractFloat} =
    isequal(x, y) | (iszero(x) & iszero(y)) | (isnan(x) & isnan(y))

maybe_neutral(x::Int) = -1 ≤ x ≤ 1 ? Neutral{x}() : x
maybe_neutral(x::Integer) = x

signed_type(::Type{T}) where {T<:Real} = T
signed_type(::Type{Complex{T}}) where {T} = Complex{signed_type(T)}
signed_type(::Type{Rational{T}}) where {T} = Rational{signed_type(T)}
# NOTE Not all versions of Julia implement `signed(T)`.
for (U, S) in (:UInt8 => :Int8, :UInt16 => :Int16, :UInt32 => :Int32,
               :UInt64 => :Int64, :UInt128 => :Int128)
    @eval signed_type(::Type{$U}) = $S
end
