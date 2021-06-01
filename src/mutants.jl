const XIntV = Union{XInt, Nothing}

_vec(n::Integer) = Vector{Limb}(undef, n)
@inline vec(x::XInt) = x.v::Vector{Limb}

lenvec(x::XSigned) = len(x), vec(x)

vec!(x::XInt, n::Integer) =
    if is_short(x)
        _vec(n)
    else
        vec!(vec(x), n)
    end

function vec!(xv::Vector, n::Integer)
    len = length(xv)
    if n > len
        Base._growend!(xv, n-len)
    end
    xv
end

vec!(::Nothing, n::Integer) = _vec(n)

# copy x into r, allocating for r when r===nothing
# assumes !is_short(x)
_copy!(r::XIntV, x::XSigned) =
    if r === x
        x
    else
        xl, xv = lenvec(x)
        _XInt(flipsign(xl, _sign(x)), _copy!(vec!(r, xl), xv, 1:xl))
    end

function _copy!(r::Vector, xv::Vector, span::UnitRange)
    a, b = first(span), last(span)
    if r !== xv
        unsafe_copyto!(r, a, xv, a, b-a+1)
    end
    r
end

function _copy!(r::Vector, xv::SVec, span::UnitRange)
    for i=span
        @inbounds r[i] = xv[i]
    end
    r
end

@inline function assign!(r::XIntV, vals::T...) where T
    v = vec!(r, length(vals))
    for i = eachindex(vals)
        @inbounds v[i] = vals[i] % Limb
    end
    v
end

@inline XInt!(r::XIntV, z::Short) =
    fits(z) ? _XInt(z % SLimb) :
              _XInt(flipsign(one(SLimb), z), assign!(r, z))

# make a XInt into r, with value -z
@inline XInt_neg!(r::XIntV, z::Limb) =
    fits(z) ? _XInt(-z % SLimb) :
              _XInt(-one(SLimb), assign!(r, z))

@inline XInt!(r::XIntV, z::Limb, flip::SLimb) =
    flip < 0 ?
        XInt_neg!(r, z) :
        XInt!(r, z)


@inline XInt!(r::XIntV, z::SLimbW, extra::SLimb=0) =
    # @assert extra >= 0
    if slimbmin < z <= slimbmax
        _XInt(z % SLimb)
    else
        XInt_big!(r, z, extra)
    end

@noinline function XInt_big!(r::XIntV, z::SLimbW, extra::SLimb)
    # @assert extra >= 0
    zz = abs(z)
    z1 = zz % Limb
    z2 = (zz >>> BITS_PER_LIMB) % Limb
    if iszero(z2)
        rv = vec!(r, 1+extra)
        @inbounds rv[1] = z1
        _XInt(sign(z) % SLimb, rv)
    else
        rv = vec!(r, 2+extra)
        @inbounds rv[1] = z1
        @inbounds rv[2] = z2
        _XInt(flipsign(SLimb(2), z), rv)
    end
end

XInt!(r::XIntV, z::LimbW, extra::SLimb=0) =
    # @assert extra >= 0
    if z <= slimbmax
        _XInt(z % SLimb)
    else
        z1 = z % Limb
        z2 = (z >>> BITS_PER_LIMB) % Limb
        if iszero(z2)
            rv = vec!(r, 1+extra)
            @inbounds rv[1] = z1
            _XInt(SLimb(1), rv)
        else
            rv = vec!(r, 2+extra)
            @inbounds rv[1] = z1
            @inbounds rv[2] = z2
            _XInt(SLimb(2), rv)
        end
    end

@inline function normalize(v::Vector, l::Integer)
    # @assert l <= length(v)
    while l > 0
        iszero(@inbounds v[l]) || break
        l -= 1
    end
    l
end

function add1!(r::XIntV, x::XSigned, y::Short)
    # @assert !is_short(x)
    samesign = signbit(x) == signbit(y)
    if samesign
        _add1!(r, x, abs(y) % Limb)
    else
        _sub1!(r, x, abs(y) % Limb)
    end
end

function _add1!(r::XIntV, x::XSigned, y::Limb)
    xl = len(x)
    rv = vec!(r, xl+1)
    c = MPN.add_1(rv, x=>xl, y)
    @inbounds rv[xl+1] = c
    rl = xl + !iszero(c)
    _XInt(flipsign(rl, _sign(x)), rv)
end

function _sub1!(r::XIntV, x::XSigned, y::Limb)
    xl = len(x)
    # we know that abs(x) > y, as y comes from a SLimb, whose absolute value
    # is < |typemmin(SLimb)| == limb1min (upper bit of y is not set)
    if xl == 1
        xv = vec(x)
        # xv[1] >= limb1min by specification
        rv1 = @inbounds xv[1] - y
        XInt!(r, rv1, _sign(x))
    else
        # if xl > 1, we see that x-y can't be an immediate integer
        rv = vec!(r, xl)
        MPN.sub_1(rv, x=>xl, y)
        rl = xl-iszero(@inbounds rv[xl])
        _XInt(flipsign(rl, _sign(x)), rv)
    end
end

_widen(x::XSigned) = widen(short(x))
_promote(x::XInt) = x
_promote(x::BitInteger) = Static(x)

@inline add!(r::XIntV, x, y) = add!(r, _promote(x), _promote(y))

@inline function add!(r::XIntV, x::XSigned, y::XSigned)
    xshort = is_short(x)
    yshort = is_short(y)
    if xshort & yshort
        XInt!(r, _widen(x) + _widen(y))
    elseif xshort
        iszero(x) ? XInt(y) : add1!(r, y, short(x))
    elseif yshort
        iszero(y) ? XInt(x) : add1!(r, x, short(y))
    else
        addbig!(r, x, y)
    end
end

# fast path for sum
# this allocate in x even if x == 0
# (i.e. this doesn't return the other arg y in this case, so no aliasing)
@inline function addbig_positive!(x::XInt, y::XInt)
    if iszero(x.x)
        yl, yv = lenvec(y)
        xv = _vec(yl+2) # +1 for later invocation which requests it, and +1 for margin
        unsafe_copyto!(xv, 1, yv, 1, yl)
        return _XInt(yl, xv)
    end
    xl, xv = lenvec(x)
    yl, yv = lenvec(y)
    rv = xv # result in x, even if we have to swap the arguments
    if xl < yl
        xl, yl = yl, xl
        xv, yv = yv, xv
    end
    rv = vec!(rv, xl+1)
    c = MPN.add(rv, xv=>xl, yv=>yl) # c ∈ (0, 1)
    @inbounds rv[xl+1] = c
    _XInt(xl + c % SLimb, rv)
end

# NOTE: this is still unfortunately roughly 2x slower than MPZ.add! for BigInt
# we recover a lot of perfs if we inline instead, but that's a big function...
@inline function addbig!(r::XIntV, x::XSigned, y::XSigned)
    xl, xv = lenvec(x)
    yl, yv = lenvec(y)
    xz, yz = _sign(x), _sign(y)
    if xl < yl
        # we don't just exchange the variables within the main function to
        # avoid type-unstability
        addbig!(r, yl, yv, yz, xl, xv, xz)
    else
        addbig!(r, xl, xv, xz, yl, yv, yz)
    end
end

@noinline function addbig!(r::XIntV, xl, xv, xz, yl, yv, yz)
    if xz == yz
        rv = vec!(r, xl+1)
        c = MPN.add(rv, xv=>xl, yv=>yl) # c ∈ (0, 1)
        @inbounds rv[xl+1] = c
        _XInt(flipsign(xl + c % SLimb, xz), rv)
    elseif xl >= yl+2 # >= 3
        # we are sure that the result will have length xl or xl-1
        rv = vec!(r, xl)
        MPN.sub(rv, xv=>xl, yv=>yl)
        rl = xl - iszero(@inbounds rv[xl])
        _XInt(flipsign(rl, xz), rv)
    else
        local xvl, yvl
        flip = false
        if xl == yl
            # same length, need to compare the content; we could use:
            # MPN.cmp(x=>xl, y=>yl) % Int
            # but we can as well do it manually, to record an upper bound on rl
            while xl > 0
                xvl = @inbounds xv[xl]
                yvl = @inbounds yv[xl]
                if xvl != yvl
                    if xvl < yvl
                        flip = true
                    end
                    break
                end
                xl -= 1
            end
            if xl == 0
                return _XInt(0)
            elseif xl == 1
                if flip
                    return XInt!(r, yvl-xvl, yz)
                else
                    return XInt!(r, xvl-yvl, xz)
                end
            end
            yl = xl
        else # xl == yl+1
            xvl = @inbounds xv[xl]
            yvl = zero(Limb)
        end
        if flip
            _addbig!(r, yl, yv, yz, yvl, xl, xv, xz, xvl)
        else
            _addbig!(r, xl, xv, xz, xvl, yl, yv, yz, yvl)
        end
    end
end

@inline function _addbig!(r, xl, xv, xz, xvl, yl, yv, yz, yvl)
    # here, xvl > yvl && xl >= 2
    rvl = xvl - yvl # value of rv[xl] "so far"
    @inbounds if rvl == 1
        rv1, c = Base.sub_with_overflow(xv[1], yv[1])
        if c && fits(rv1) # above limbs could cancel out, check if result is immediate
            i = 2
            local ri::Limb
            while i < xl
                ri, c2 = Base.sub_with_overflow(xv[i], yv[i])
                ri, c = ri-c,
                        c2 | c & iszero(ri)
                iszero(ri) || break
                # at this point (ri==0), we can see that c has the same value as c2,
                # but letting c = c2 above is not enough, as we re-use c later for
                # the "real" computation, so it must be set according to the general
                # case
                i += 1
            end
            # i == xl || ri != 0
            if i == xl && c
                return _XInt(flipsign(rv1 % SLimb, xz)) # we know that rv1 fits
            else
                rv = vec!(r, xl)
                rv[1] = rv1
                fill!(@view(rv[2:i-1]), zero(Limb))
                if i == xl # !c, as the case c==true was handled above
                    rv[xl] = rvl
                    rl = xl
                else
                    rv[i] = ri
                    # we would like to use native MPN.sub_n, but we can't pass to it
                    # a pre-existing carry
                    c = MPN.sub_n(rv, xv, yv, i+1:xl-1, c)
                    rv[xl] = rvl-c
                    rl = normalize(rv, xl)
                end
                return _XInt(flipsign(rl, xz), rv)
            end
        end
    end
    @assert xl == yl || xl == yl+1
    rv = vec!(r, xl)
    c = MPN.sub_n(rv, xv, yv, yl)
    if xl > yl
        rv[xl] = @inbounds(xv[xl]-c)
    end
    rl = normalize(rv, xl)
    _XInt(flipsign(rl, xz), rv)
end

add!(x::XInt, y) = add!(x, x, _promote(y))

neg!(x::XInt) = _XInt(-x.x, x.v)

sub!(r::XIntV, x, y::XInt) = add!(r, _promote(x), neg!(y))
# we don't implement neg!(s::Static), as s might contain unsigned, or typemin(SLimb)
sub!(r::XIntV, x::XInt, y::BitInteger) = neg!(add!(r, neg!(x), Static(y)))

sub!(x::XInt, y) = sub!(x, x, _promote(y))

is_limb(x::XSigned) = is_short(x) # we don't bother for non-short with one limb
is_limb(x::ShortMax) = true
limb(x::XSigned) = short(x)
limb(x::SLimbMax) = x % SLimb
limb(x::ULimbMax) = x % Limb
_widen(x::ShortMax) = SLimbW(x)
_sign(x::Limb) = SLimb(1)
_sign(x::SLimb) = sign(x)

mul!(x::XInt, y::Union{ShortMax,XInt}) = mul!(x, x, y)

@inline function mul!(r::XIntV, x::XInt, y::Union{ShortMax,XInt})
    xshort = is_short(x)
    yshort = is_limb(y)
    if xshort & yshort
        XInt!(r, _widen(x) * _widen(y))
    elseif xshort
        mul1!(r, y, short(x))
    elseif yshort
        mul1!(r, x, limb(y))
    else
        mulbig!(r, x, y)
    end
end

function mul1!(r::XIntV, x::XInt, y::Short)
    # @assert !is_short(x) # y can be slimbmin
    iszero(y) && return XInt(0)
    isone(y) && return x
    y == -1 && return neg!(x)
    sz = flipsign(_sign(x), _sign(y))
    xl = len(x)
    rv = vec!(r, xl + 1)
    high = MPN.mul_1(rv, x, abs(y) % Limb) # rv === vec(x) is supported
    @inbounds rv[xl+1] = high
    _XInt(flipsign(xl + !iszero(high), sz), rv)
end

function mulbig!(r::XIntV, x::XInt, y::XInt)
    # @assert !is_short(x) && !is_short(y)
    xl, xv = lenvec(x)
    yl, yv = lenvec(y)
    sz = flipsign(_sign(x), _sign(y))
    if xl < yl
        xl, yl = yl, xl
        xv, yv = yv, xv
    end

    tv = rv = vec!(r, xl+yl)
    # check for aliasing
    if rv === xv
        # MPN can't do mpn_mul inplace; rv is already big enough to hold the result,
        # so copy xv to a temporary, which can be discarded afterwards
        tv = tmpvec(xl)
        unsafe_copyto!(tv, 1, xv, 1, xl)
        xv = tv
        if rv === yv
            # assume xl == yl; make yv egal again to xv, the square will be computed
            yv = xv
        end
    elseif rv === yv
        tv = tmpvec(yl)
        unsafe_copyto!(tv, 1, yv, 1, yl)
        yv = tv
    end
    high = MPN.mul(rv, xv => xl, yv => yl)
    tv !== rv && freetmpvec(tv)
    _XInt(flipsign(xl+yl-iszero(high), sz), rv)
end

# set r to ~x == -(x+1)
com!(r::XIntV, x::XInt=r) =
    if is_short(x)
        if x.x !== slimbmax
            _XInt(~x.x)
        else
            rv = vec!(r, 1)
            @inbounds rv[1] = limb1min
            _XInt(-one(SLimb), rv)
        end
    else
         neg!(add1!(r, x, one(SLimb)))
    end

lshift!(x::XInt, c::Integer) = lshift!(x, x, c)

# from base/operators.jl
@inline function lshift!(r::XIntV, x::XInt, c::Integer)
    typemin(Cint) <= c <= typemax(Cint) && return lshift!(r, x, c % Cint)
    (x >= 0 || c >= 0) && return zero(XInt)
    XInt(-1)
end

@inline lshift!(r::XIntV, x::XInt, c::Unsigned) =
    c <= typemax(Cuint) ? lshift!(r, x, c % Cuint) : zero(XInt)

@inline lshift!(r::XIntV, x::XInt, c::Cint) =
    c >= 0 ? lshift!(r, x, unsigned(c)) : rshift!(r, x, unsigned(-c))

@inline function lshift!(r::XIntV, x::XInt, c::Cuint)
    z = x.x
    iszero(z) && return x # NOTE: needs updating if a reduce argument is added
    if is_short(x)
        iszero(c) && return x
        if z > 0
            leading_zeros(z) > c &&
                return _XInt(z << c)
        else
            if leading_ones(z) > c
                s = z << c
                s !== slimbmin &&
                    return _XInt(z << c)
                # NOTE: it seems to be almost 2x faster for the general case to not
                # return the (known) result here for s==slimbmin, but rather to let
                # this special case be handled by lshift_small!
            end
        end
        lshift_small!(r, z, c)
    else
        lshift_big!(r, x, c)
    end
end

@noinline function lshift_small!(r::XIntV, z::SLimb, c::Cuint)
    zu = abs(z) % Limb
    offset = _divLimb(c) % SLimb
    cnt = _modLimb(c) % SLimb
    rl = 1+offset
    if iszero(cnt)
        rv = vec!(r, rl)
        @inbounds rv[rl] = zu
    else
        rv = vec!(r, rl+1)
        w = widen(zu) << cnt
        @inbounds rv[rl] = w % Limb
        high = @inbounds rv[rl+1] = (w >> BITS_PER_LIMB) % Limb
        rl += !iszero(high)
    end
    fill!(@view(rv[1:offset]), Limb(0))
    _XInt(flipsign(rl, z), rv)
end

@noinline function lshift_big!(r::XIntV, x::XInt, c::Cuint)
    r === x && c == 0 && return x
    xl = len(x)
    xv = vec(x)
    offset = _divLimb(c) % SLimb
    cnt = _modLimb(c) % SLimb
    rl = xl+offset
    if iszero(cnt)
        rv = vec!(r, rl)
        # TODO: when r===x and rv requires allocation anyway in vec! above,
        # maybe it would be more efficient to prepend! zeros ?
        unsafe_copyto!(rv, offset+1, xv, 1, xl)
    else
        rv = vec!(r, rl+1)
        high = MPN.lshift(@view(rv[offset+1:rl]), xv=>xl, cnt)
        @inbounds rv[rl+1] = high
        rl += !iszero(high)
    end
    fill!(@view(rv[1:offset]), Limb(0))
    _XInt(flipsign(rl, x.x), rv)
end

rshift!(x::XInt, c::Integer) = rshift!(x, x, c)

# from base/operators.jl
@inline function rshift!(r::XIntV, x::XInt, c::Integer)
    typemin(Cint) <= c <= typemax(Cint) && return rshift!(r, x, c % Cint)
    (x >= 0 || c < 0) && return zero(XInt)
    XInt(-1)
end

@inline rshift!(r::XIntV, x::XInt, c::Cint) =
    c >= 0 ? rshift!(r, x, unsigned(c)) : lshift!(r, x, unsigned(-c))

@inline function rshift!(r::XIntV, x::XInt, c::Cuint)
    z = x.x
    is_short(x) && return _XInt(z >> c)
    (iszero(z) || iszero(c)) && return x
    rshift_big!(r, x, c)
end

# For non-negative integers, right-shift is as obvious as it gets.
# For negative numbers, we use as usual the formula ~y = -(y+1) to emulate 2-complement
# integers; assuming x < 0 and c > 0, letting u = -x and v = u - 1 >= 0, we have
# x == -(v + 1) == ~v, from which we infer
# x >> c == ~v >> c == ~(v >> c) == -(v >> c + 1)
# Now, we don't want to compute v >> c, only u >> c. There are two cases:
# 1. u is a multiple of 2^c, i.e. u = k*2^c and u >> c == k
#    then v == u-1 == (k-1)*2^c + (2^c-1), therefore v >> c == k-1
#    hence: x >> c == -(k-1 + 1) == -k == -(u >> c) == -(-x >> c)
# 2. otherwise, u = k*2^c + r where 1 <= r < 2^c
#    then v == u-1 == k*2^c + r-1 where 0 <= r-1 < 2^c, therefore v >> c == u >> c
#    hence: x >> c == -(-x >> c + 1)
# Also, this can be derived more direcly from x >> c == fld(x, 2^c) where x = -k*2^c - r
@noinline function rshift_big!(r::XIntV, x::XInt, c::Cuint)
    xl = len(x)
    xv = vec(x)
    offset = _divLimb(c) % SLimb
    cnt = _modLimb(c) % SLimb
    rl = xl-offset
    neg = signbit(x.x)
    rl <= 0 && return XInt(-neg)

    rest = false # records whether there is any set bit among the first c in -x (when x < 0)
    if neg
        rest = any(!=(zero(Limb)), @view(xv[1:offset]))
    end

    if  rl <= 2 # special case, to avoid allocating for nothing
        xvend = @inbounds xv[xl] % LimbW
        if rl == 2
            xvend = xvend << BITS_PER_LIMB | @inbounds xv[xl-1] % LimbW
        end
        u = xvend >> cnt
        if neg & !rest
            rest |= trailing_zeros(xvend) < cnt
        end
        if rest && u == typemax(LimbW)
            # happens e.g. with x = -(XInt(2)^192-1) and c == 64 (with sizeof(Limb) == 8)
            _XInt(SLimb(-3), assign!(r, 0, 0, 1))
        else
            u += rest
            if u <= slimbmax
                _XInt(flipsign(u % SLimb, x.x))
            elseif u <= typemax(Limb)
                _XInt(flipsign(one(SLimb), x.x),
                      assign!(r, u % Limb))
            else
                _XInt(flipsign(SLimb(2), x.x),
                      assign!(r, u % Limb , (u >> BITS_PER_LIMB) % Limb))
            end
        end
    else
        rv = vec!(r, rl + neg)
        if iszero(cnt)
            unsafe_copyto!(rv, 1, xv, offset+1, rl)
        else
            discarded = MPN.rshift(rv=>rl, @view(xv[offset+1:xl]), cnt)
            if neg
                rest |= !iszero(discarded)
            end
            rl -= iszero(@inbounds rv[rl])
        end
        if rest
            d = MPN.add_1(rv, rv=>rl, Limb(1))
            @inbounds rv[rl+1] = d
            rl += !iszero(d)
        end
        _XInt(flipsign(rl, x.x), rv)
    end
end

@inline and!(r::XIntV, x, y) = and!(r, _promote(x), _promote(y))

@inline and!(x::XInt, y::Union{ShortMax,XSigned}) = and!(x, x, y)

@inline function and!(r::XIntV, x::Union{ShortMax,XSigned}, y::Union{ShortMax,XSigned})
    xshort = is_limb(x)
    yshort = is_limb(y)
    if xshort & yshort
        XInt!(r, limb(x) & limb(y)) # if y is unsigned, result of & is also unsigned and
                                    # XInt! does the right thing
    elseif xshort
        iszero(x) ? _XInt(0) : and_small!(r, y, limb(x))
    elseif yshort
        iszero(y) ? _XInt(0) : and_small!(r, x, limb(y))
    else
        and_big!(r, x, y)
    end
end

function and_small!(r::XIntV, x::XInt, y::Limb)
    xv = vec(x)
    x1 = @inbounds xv[1]
    if ispos(x)
        XInt!(r, x1 & y)
    else
        # x & y = ~(-x - 1) & y
        XInt!(r, ~(x1-1) & y)
    end
end

@noinline function and_small!(r::XIntV, x::XSigned, y::SLimb)
    # @assert !iszero(x) && !iszero(y) && !is_short(x) && is_short(y)
    # y is short, but can also be typemin(SLimb)
    xl, xv = lenvec(x)
    yy = y % Limb
    x1 = @inbounds xv[1]
    if ispos(x)
        if y > 0
            # x & y <= min(x, y) == y, so the result is short
            _XInt(x1 & yy)
        else # x > 0, y < 0
            u = x1 & yy
            res = _copy!(r, x)
            rv = vec(res)
            @inbounds rv[1] = u
            # @assert_reduced x # if x is not reduced, the result could be immediate
            res
        end
    elseif y > 0 # x < 0
        # x & y = ~(-x - 1) & y; result >= 0, and <= y, so is immediate
        _XInt((~(x1-1) & yy) % SLimb)
    else # x < 0, y < 0
        # let u = -x: -u & y = ~(u-1) & y = ~(u-1 | ~y) = -(u-1 | ~y) - 1
        # the result is < 0, and it's easy to see that it's also <= min(x, y), so
        # it can't be an immediate integer (provided x isn't)

        if iszero(x1)
            # if x1 == 0, we see that a 2-complement representation of x would also
            # have a null first limb, so x & y == x
            XInt(x)
        else
            # x1 > 0, so x-1 differs from x only in the 1st limb
            r1 = (x1-1) | ~y
            if r1 == typemax(Limb)
                # +1 overflows, so we need to allocate one more limb, just in case
                rv = vec!(r, xl+1)
                @inbounds rv[1] = zero(Limb)
                carry = true
                @inbounds for i=2:xl
                    u = xv[i]
                    if carry && u == typemax(Limb)
                        rv[i] = zero(Limb)
                    else
                        rv[i] = u+carry
                        carry = false
                    end
                end
                @inbounds rv[xl+1] = carry
                rl = xl + carry
                _XInt(-rl, rv)
            else
                rv = vec!(r, xl)
                _copy!(rv, xv, 2:xl)
                @inbounds rv[1] = r1+1
                _XInt(flipsign(xl, _sign(x)), rv)
            end
        end
    end
end

@noinline function and_big!(r::XIntV, x::XSigned, y::XSigned)
    # @assert !iszero(x) && !iszero(y) && !is_short(x) && !is_short(y)
    if ispos(x)
        if ispos(y)
            xl, xv = lenvec(x)
            yl, yv = lenvec(y)
            if xl < yl
                xv, yv = yv, xv
                xl, yl = yl, xl
            end
            rl = yl
            local rvl # stores the last limb in r
            @inbounds while rl > 0
                rvl = xv[rl] & yv[rl]
                iszero(rvl) || break
                rl -= 1
            end
            if rl <= 1
                XInt!(r, rvl)
            else
                rv = vec!(r, rl)
                # MPN.and_n(rv, xv, yv, rl)
                for idx = 1:rl
                    # we already computed the value of the last iteration, but
                    # it seems no more expensive to just recompute it in this loop
                    @inbounds rv[idx] = xv[idx] & yv[idx]
                end
                _XInt(rl, rv)
            end
        else # x > 0, y < 0
            x, y = y, x
            @goto mixed
        end
    elseif ispos(y) # x < 0
        @label mixed
        # result is positive
        # x & y = ~(-x - 1) & y
        xl, xv = lenvec(x)
        yl, yv = lenvec(y)
        if yl <= xl
            # we don't know the resulting rl in advance; on the high limbs of -x,
            # we don't know yet the effect of `-1`. So we first scan from the low
            # end: as long as x's limbs are 0, they become 0xF...F after `-1`, and
            # 0 after `~`, so r's corresponding limbs are 0.
            i = 1
            local xi
            while i <= yl
                xi = @inbounds xv[i]
                iszero(xi) || break
                i += 1
            end
            if yl < i
                _XInt(0)
            else
                rl = yl
                local rvl
                # we scan from the high end to compute rl: above i, the `-1` had no effect,
                # and we search for the hightest non-zero limb in r
                while rl > i
                    rvl = @inbounds ~xv[rl] & yv[rl]
                    iszero(rvl) || break
                    rl -= 1
                end
                if rl == i
                    # all the limbs of r above and below i are 0
                    rvl = @inbounds ~(xi-1) & yv[i]
                    if iszero(rvl)
                        rl = 0
                    end
                end
                if rl <= 1
                    XInt!(r, rvl)
                else
                    rv = vec!(r, rl)
                    for j = 1:i-1
                        @inbounds rv[j] = zero(Limb)
                    end
                    if i < rl
                        @inbounds rv[i] = ~(xv[i]-1) & yv[i] # rvl if i == rl
                        for j = i+1:rl-1
                            @inbounds rv[j] = ~xv[j] & yv[j]
                        end
                    end
                    @inbounds rv[rl] = rvl
                    _XInt(rl, rv)
                end
            end
        else # yl > xl
            # no need to scan, we know that rl == yl
            rv = vec!(r, yl)
            xok = false
            @inbounds for i = 1:xl
                xi = xv[i]
                yi = yv[i]
                if xok
                    rv[i] = ~xi & yi
                else
                    xok = !iszero(xi)
                    rv[i] = ~(xi-1) & yi
                end
            end
            for i = xl+1:yl
                @inbounds rv[i] = yv[i]
            end
            _XInt(yl, rv)
        end
    else # x < 0, y < 0
        # result is negative
        # -u & -v = ~(u-1) & ~(v-1) = ~(u-1 | v-1) = -(u-1 | v-1) - 1
        xl, xv = lenvec(x)
        yl, yv = lenvec(y)
        if xl < yl
            xv, yv = yv, xv
            xl, yl = yl, xl
        end
        rl = xl
        rv = vec!(r, rl+1)
        xok, yok, oneok = false, false, false
        for i=1:xl
            xi = @inbounds xv[i]
            yi = i <= yl ? @inbounds(yv[i]) : zero(Limb)
            if !xok
                xok = !iszero(xi) # carry won't propagate anymore
                xi -= 1
            end
            if !yok
                yok = !iszero(yi)
                yi -= 1
            end
            u = xi | yi
            if !oneok
                oneok = u != typemax(Limb)
                u += 1
            end
            @inbounds rv[i] = u
        end
        if !oneok
            rl += 1
            @inbounds rv[rl] = one(Limb)
        end
        _XInt(-rl, rv)
    end
end

## ior (|)

@inline ior!(r::XIntV, x, y) = ior!(r, _promote(x), _promote(y))
@inline ior!(x::XInt, y::Union{ShortMax,XSigned}) = ior!(x, x, y)

@inline function ior!(r::XIntV, x::Union{ShortMax,XSigned}, y::Union{ShortMax,XSigned})
    xshort = is_limb(x)
    yshort = is_limb(y)
    if xshort & yshort
        x1 = limb(x)
        y1 = limb(y)
        r1 = x1 | y1
        if x1 >= 0 && y1 >= 0 # result is >= 0
            XInt!(r, unsigned(r1))
        else # result is < 0
            XInt!(r, signed(r1))
        end
    elseif xshort
        iszero(x) ? XInt(y) : ior_small!(r, y, limb(x))
    elseif yshort
        iszero(y) ? XInt(x) : ior_small!(r, x, limb(y))
    else
        ior_big!(r, x, y)
    end
end

@noinline function ior_small!(r::XIntV, x::XSigned, y::Short)
    # @assert !iszero(x) && !iszero(y) && !is_short(x) && is_short(y)
    # y is small
    xl, xv = lenvec(x)
    yy = y % Limb
    x1 = @inbounds xv[1]
    if ispos(x)
        if y > 0
            res = _copy!(r, x)
            rv = vec(res)
            @inbounds rv[1] = x1 | yy
            res
        else # x > 0, y < 0
            # when fits(y), y is short, so more than its sign bit is set,
            # and x | y >= y (result is short); but when y doesn't come
            # from a XInt, y==slimbmin is possible, so result is not
            # guarranteed to be short
            # _XInt(x1 | yy) # when fits(y)
            XInt!(r, (x1 % SLimb) | y)
        end
    elseif y > 0 # x < 0
        # x | y = ~(-x - 1) | y = ~((-x - 1) & ~y) = -((-x - 1) & ~y) - 1
        carry = iszero(x1)
        r1 = (x1-1) & ~yy + 1
        # a small analysis shows that, given y > 0, the `+1` can't carry over upper limbs

        if xl == 1
            # then !carry as -x > 0
            XInt_neg!(r, r1)
        else
            rv = vec!(r, xl)
            @inbounds rv[1] = r1
            @inbounds for i=2:xl
                xi = xv[i]
                rv[i] = xi - carry
                carry &= iszero(xi)
            end
            rl = xl - iszero(@inbounds rv[xl])
            _XInt(-rl, rv)
        end
    else # x < 0, y < 0
        # x | y = ~(-x-1) | y # similar to x > 0, y < 0
        # _XInt(~(x1-1) | yy)
        XInt!(r, (~(x1-1) % SLimb) | y)
        XInt!(r, (~(x1-1) | yy) % SLimb)
    end
end

@noinline function ior_big!(r::XIntV, x::XSigned, y::XSigned)
    # @assert !iszero(x) && !iszero(y) && !is_short(x) && !is_short(y)
    # we keep here (and in and_big!) some type instabilities if
    # typeof(x) != typeof(y), but the overhead is not that bad, and might
    # not be concerning enough to warrant type-stabilizing this function
    # (like we did for addbig!)
    if ispos(x)
        if ispos(y) # r > 0
            xl, xv = lenvec(x)
            yl, yv = lenvec(y)
            if xl < yl
                xv, yv = yv, xv
                xl, yl = yl, xl
            end
            rv = vec!(r, xl)
            for i=1:yl
                @inbounds rv[i] = xv[i] | yv[i]
            end
            for i=yl+1:xl
                @inbounds rv[i] = xv[i]
            end
            _XInt(xl, rv)
        else # x > 0, y < 0 : r < 0
            x, y = y, x
            @goto mixed
        end
    elseif ispos(y) # x < 0 : r < 0
        @label mixed
        # x | y = ~(-x - 1) | y = ~((-x - 1) & ~y) = -((-x - 1) & ~y) - 1
        xl, xv = lenvec(x)
        yl, yv = lenvec(y)
        if yl + 2 <= xl
            # then -x-1 still has at least one more limb than y, which is not cancelled
            # when &-ed with ~y; then rl could be xl, or xl-1 when xv[l] == 1 and
            # xv[l-1] == 0
            rv = vec!(r, xl)
            cm = cp = true # carries for -1 and +1
            @inbounds for i=1:yl
                xi = xv[i]
                yi = yv[i]
                ri = (xi - cm) & ~yi + cp
                cm &= iszero(xi)
                cp &= iszero(ri) # note: !cp ==> !cm, i.e. cm can't last longer than cp
                rv[i] = ri
            end
            # at this point, we know for sure that !cp
            # bewond y's limbs, ~y is all ones, so we just write x limbs, carrying out cm
            for i=yl+1:xl
                xi = xv[i]
                rv[i] = xi - cm
                cm &= iszero(xi)
            end
            rl = xl - iszero(@inbounds rv[xl])
            _XInt(-rl, rv)
        else # yl >= xl - 1
            # rl could be anything, e.g.  -(2^128) | (2^128-1) == -1
            # so the idea is to scan from the end to find the highest non-zero limb
            # but for this, we need to know where the carry from `-1` stops: this is the
            # first non-zero position in xv, call it k; we therefore need to first scan
            # from the beginning to find k, and then from the end with the
            # formula xi & ~yi; if it happens that this is all zero beyond k, we would
            # then need to scan again from the beginning to find rl, before allocating;
            # this is a rare case, so we might not be concerned with having to scan
            # twice from the beginning; but for simplicity, in the first scan from the
            # beginning, we also record the highest non-zero ri upto k (this is a bit
            # more expensive than just finding the first non-zero xi, but in general
            # this loop won't have many iterations)
            cm = cp = true # carries for -1 and +1
            i = 0 # the first non-zero position in xv
            rl = 0
            @inbounds while cm
                i += 1
                xi = xv[i]
                yi = i > yl ? zero(Limb) : yv[i]
                ri = (xi - cm) & ~yi + cp
                cm &= iszero(xi)
                cp &= iszero(ri)
                if !iszero(ri)
                    rl = i
                end
            end
            k = i
            # beyond i, the formula is xi & ~yi: we scan from the end to find the first non-0
            i = xl
            @inbounds while i > k
                yi = i > yl ? zero(Limb) : yv[i]
                iszero(xv[i] & ~yi) || break
                i -= 1
            end
            # so far, rl points at the highest non-zero limb upto k in the result
            if i != k # not all zero above k
                rl = i
            end
            # we are now ready to store the result
            if rl == 1
                r1 = @inbounds (xv[1]-1) & ~yv[1] + 1
                XInt_neg!(r, r1)
            else
                rv = vec!(r, rl)
                cm = cp = true # carries for -1 and +1
                @inbounds for i=1:rl
                    xi = xv[i]
                    yi = i > yl ? zero(Limb) : yv[i]
                    ri = (xi - cm) & ~yi + cp
                    cm &= iszero(xi)
                    cp &= iszero(ri)
                    rv[i] = ri
                end
                _XInt(-rl, rv)
            end
        end
    else # x < 0, y < 0 : r < 0
        # -u | -v = ~(u-1) | ~(v-1) = ~(u-1 & v-1) = -(u-1 & v-1) - 1
        # we do a scan, similar to what we do for x < 0, y > 0 and yl >= xl - 1
        xl, xv = lenvec(x)
        yl, yv = lenvec(y)
        if xl < yl
            xv, yv = yv, xv
            xl, yl = yl, xl
        end

        cx, cy, cp = true, true, true
        i = 0
        rl = 0
        while (cx | cy) && i < yl
            i += 1
            xi = @inbounds xv[i]
            yi = @inbounds yv[i]
            u = (xi-cx) & (yi-cy) + cp
            if !iszero(u)
                rl = i
            end
            cx &= iszero(xi)
            cy &= iszero(yi)
            cp &= iszero(u) # cp = cx & cy would also work
        end
        k = i
        i = yl
        @inbounds while i > k
            iszero(xv[i] & yv[i]) || break
            i -= 1
        end
        if i > k
            rl = i
        end
        if rl == 1
            r1 = @inbounds (xv[1]-1) & (yv[1]-1) + 1
            XInt_neg!(r, r1)
        else
            rv = vec!(r, rl)
            cx, cy, cp = true, true, true
            @inbounds for i=1:rl
                xi = xv[i]
                yi = yv[i]
                rv[i] = u = (xi-cx) & (yi-cy) + cp
                cx &= iszero(xi)
                cy &= iszero(yi)
                cp &= iszero(u)
            end
            _XInt(-rl, rv)
        end
    end
end
