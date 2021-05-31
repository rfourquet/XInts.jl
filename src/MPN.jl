module MPN

import ..XInts: lenvec, vec
using ..XInts: XInt, SVec

using Base.GC: @preserve
using Base.GMP: Limb # mp_limb_t
const PLimb = Ptr{Limb}
const Size = Clong # mp_size_t

len(p::Pair) = p[2]
ptr(p::Pair) = ptr(p[1])
lenvec(p::Pair) = p[2], vec(p[1])

vec(x::Vector) = x
vec(x::SVec) = x
ptr(p::Ptr) = p
len(p::AbstractArray) = length(p)
ptr(p::AbstractArray) = pointer(p) # Vector and views thereof

len(b::BigInt) = abs(b.size)
ptr(b::BigInt) = b.d
lenvec(b::BigInt) = len(b), b

isheap(x) = false
isheap(x::XInt) = true
isheap(x::BigInt) = true
isheap(x::Vector) = true
@inline isheap(x, y) = isheap(x) & isheap(y)

add_1(rp::PLimb, s1::PLimb, n, s2::Limb) = ccall((:__gmpn_add_1, :libgmp), Limb,
                                                 (PLimb, PLimb, Size, Limb),
                                                 rp, s1, n, s2)

add(rp::PLimb, s1::PLimb, l1, s2::PLimb, l2) = ccall((:__gmpn_add, :libgmp), Limb,
                                                     (PLimb, PLimb, Size, PLimb, Size),
                                                     rp, s1, l1, s2, l2)

sub_1(rp::PLimb, s1::PLimb, n, s2::Limb) = ccall((:__gmpn_sub_1, :libgmp), Limb,
                                                 (PLimb, PLimb, Size, Limb),
                                                 rp, s1, n, s2)

sub(rp::PLimb, s1::PLimb, l1, s2::PLimb, l2) = ccall((:__gmpn_sub, :libgmp), Limb,
                                                     (PLimb, PLimb, Size, PLimb, Size),
                                                     rp, s1, l1, s2, l2)

sub_n(rp::PLimb, s1::PLimb, s2::PLimb, n) = ccall((:__gmpn_sub_n, :libgmp), Limb,
                                                  (PLimb, PLimb, PLimb, Size),
                                                  rp, s1, s2, n)

cmp(s1, s2, n=len(s1)) = @preserve s1 s2 ccall((:__gmpn_cmp, :libgmp), Cint,
                                               (Ptr{Limb}, Ptr{Limb}, Clong),
                                               ptr(s1), ptr(s2), n)

lshift(rp, s1, c) = @preserve rp s1 ccall((:__gmpn_lshift, :libgmp), Limb,
                                          (PLimb, PLimb, Size, Cuint),
                                          ptr(rp), ptr(s1), len(s1), c)

rshift(rp, s1, c) = @preserve rp s1 ccall((:__gmpn_rshift, :libgmp), Limb,
                                          (PLimb, PLimb, Size, Cuint),
                                          ptr(rp), ptr(s1), len(s1), c)

and_n(rp, s1, s2, n=len(s1)) = @preserve rp s1 s2 ccall((:__gmpn_and_n, :libgmp), Cvoid,
                                                        (PLimb, PLimb, PLimb, Size),
                                                        ptr(rp), ptr(s1), ptr(s2), n)

mul_1(rp, s1, s2limb) = @preserve rp s1 ccall((:__gmpn_mul_1, :libgmp), Limb,
                                              (PLimb, PLimb, Size, Limb),
                                              ptr(rp), ptr(s1), len(s1), s2limb)

mul(rp, s1, s2) = @preserve rp s1 s2 ccall((:__gmpn_mul, :libgmp), Limb,
                                           (PLimb, PLimb, Size, PLimb, Size),
                                           ptr(rp), ptr(s1), len(s1), ptr(s2), len(s2))


@inline function add_1(rv::Vector, x, y::Limb)
    xl, xv = lenvec(x)
    if isheap(xv)
        @preserve rv x add_1(ptr(rv), ptr(xv), xl, y) % Bool
    else
        add_1(rv, xv, xl, y)
    end
end

@inline function add_1(rv::Vector, xv, xl, y)
    @inbounds rv[1], c =  Base.add_with_overflow(xv[1], y)
    for i=2:xl
        ri = @inbounds xv[i]
        @inbounds rv[i] = ri + c
        c &= ri == typemax(Limb)
    end
    c
end

@inline function add(rp::Vector, x, y)
    xl, xv = lenvec(x)
    yl, yv = lenvec(y)
    # native MPN is not really faster than non-inlined Julia version here,
    # but if we inline Julia version (like we do now), there is no reason
    # to use MPN version
    use_MPN = false
    if use_MPN && isheap(xv, yv)
        @preserve rp xv yv add(ptr(rp), ptr(xv), xl, ptr(yv), yl) % Bool
    else
        add(rp, xv, xl, yv, yl)
    end
end

@inline function add(rv, xv, xl, yv, yl)
    # @assert xl >= yl
    c = false
    for i=1:yl
        xi = @inbounds xv[i]
        yi = @inbounds yv[i]
        ri, c2 = Base.add_with_overflow(xi, yi)
        @inbounds rv[i] = ri+c
        c = c2 | (c & (ri == typemax(Limb)))
    end
    for i=yl+1:xl
        ri = @inbounds xv[i]
        @inbounds rv[i] = ri + c
        c &= ri == typemax(Limb)
    end
    c
end

@inline function sub_1(rv::Vector, x, y::Limb)
    xl, xv = lenvec(x)
    if isheap(xv)
        @preserve rv x sub_1(ptr(rv), ptr(xv), xl, y) % Bool
    else
        sub_1(rv, xv, xl, y)
    end
end

@inline function sub_1(rv::Vector, xv, xl, y)
    @inbounds rv[1], c =  Base.sub_with_overflow(xv[1], y)
    for i=2:xl
        ri = @inbounds xv[i]
        @inbounds rv[i] = ri - c
        c &= iszero(ri)
    end
    c
end

@inline function sub(rp::Vector, x, y)
    xl, xv = lenvec(x)
    yl, yv = lenvec(y)
    if isheap(xv, yv)
        @preserve rp xv yv sub(ptr(rp), ptr(xv), xl, ptr(yv), yl) % Bool
    else
        sub(rp, xv, xl, yv, yl)
    end
end

@inline function sub(rv, xv, xl, yv, yl)
    # @assert xl >= yl
    c = sub_n(rv, xv, yv, 1:yl, false)
    for i=yl+1:xl
        ri = @inbounds xv[i]
        @inbounds rv[i] = ri-c
        c &= iszero(ri)
    end
    c
end


@inline function sub_n(rp::Vector, x, y, n)
    xv = vec(x)
    yv = vec(y)
    if isheap(xv, yv)
        @preserve rp xv yv sub_n(ptr(rp), ptr(xv), ptr(yv), n) % Bool
    else
        sub_n(rp, xv, yv, 1:n, false)
    end
end

@inline function sub_n(rv, xv, yv, r::AbstractUnitRange, c::Bool)
    for i=r
        xi = @inbounds xv[i]
        yi = @inbounds yv[i]
        ri, c2 = Base.sub_with_overflow(xi, yi)
        @inbounds rv[i] = ri-c
        c = c2 | (c & iszero(ri))
    end
    c
end

end # MPN
