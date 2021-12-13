using Plots
using Plots.PlotMeasures
using DelimitedFiles
using Random, Distributions

"""
Call this as jl script on main def'd at bottom.

Takes as inputs four files and int. Files should be 
ordered as gcc input, gcc output, compcert input,
compcert output. Int is the number of random points
used to generate compiler data; it is needed to 
generater the correspinding julia data.

Outputs are six plots, two for each compiler (gcc,
compcert) and two for julia jit LLVM. 
"""

fpath = @__DIR__

# formally proven bound for one step of LF integration (position)
pbnd      = 4719104053608481 / 37778931862957161709568

function plot_comps(file1, file2, file3, file4)
    """
    resource: https://docs.julialang.org/en/v1/stdlib/DelimitedFiles/
    """

    # data for gcc; read in as matrices

    in_rands_gcc = readdlm(file1, Float64)
    out_xv_gcc   = readdlm(file2, Float64)

    # turn into vectors

    vec_in_gcc    = [x::Float64 for x in in_rands_gcc]
    vec_xv_gcc    = [x::Float64 for x in out_xv_gcc]
    len           = convert(Int64,length(vec_xv_gcc)/2)
    vec_in_x_gcc  = [x for x in vec_in_gcc[1:len]]
    vec_in_v_gcc  = [v for v in vec_in_gcc[len+1:len*2]]
    vec_x_gcc     = [x for x in out_xv_gcc[1:len]]
    vec_v_gcc     = [v for v in out_xv_gcc[len+1:len*2]]

    max_x_gcc     = maximum(vec_x_gcc)

    # data for CompCert

    in_rands_cc = readdlm(file3, Float64)
    out_xv_cc   = readdlm(file4, Float64)

    vec_in_cc    = [x::Float64 for x in in_rands_cc]
    vec_xv_cc    = [x::Float64 for x in out_xv_cc]
    len          = convert(Int64,length(vec_xv_cc)/2)
    vec_in_x_cc  = [x for x in vec_in_cc[1:len]]
    vec_in_v_cc  = [v for v in vec_in_cc[len+1:len*2]]
    vec_x_cc     = [x for x in out_xv_cc[1:len]]
    vec_v_cc     = [v for v in out_xv_cc[len+1:len*2]]

    max_x_cc     = maximum(vec_x_cc)

    # plots for gcc

    plot([pbnd for i in 1:len],seriestype="vline",label="formally proven bound=$pbnd" )
    plot!([max_x_gcc for i in 1:len],seriestype="vline",label="worst empirical error=$max_x_gcc" )
    plota = histogram!(vec_x_gcc, xlabel = "floating-point error",ylabel = "frequency",
    label="empirical error",size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
    legendfontsize=12, yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12)
    savefig(plota,fpath*"/gcc_errors.png")

    plot([pbnd for i in -1:1],seriestype="hline",label="formally proven bound=$pbnd" )
    plotb = scatter!(vec_in_x_gcc,vec_x_gcc, ylabel = "floating-point error",xlabel = "position val",
    size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
    yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12, label="empirical error",
    xlims = (-1,1))
    savefig(plotb,fpath*"/gcc_errors2.png")

    # plots for CompCert

    plot([pbnd for i in 1:len],seriestype="vline",label="formally proven bound=$pbnd" )
    plot!([max_x_cc for i in 1:len],seriestype="vline",label="worst empirical error=$max_x_cc" )
    plota = histogram!(vec_x_cc, xlabel = "floating-point error",ylabel = "frequency",
    label="empirical error",size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
    legendfontsize=12, yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12)
    savefig(plota,fpath*"/cc_errors.png")

    plot([pbnd for i in -1:1],seriestype="hline",label="formally proven bound=$pbnd" )
    plotb = scatter!(vec_in_x_cc,vec_x_cc, ylabel = "floating-point error",xlabel = "position val",
    size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
    yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12, label="empirical error",
    xlims = (-1,1))
    savefig(plotb,fpath*"/cc_errors2.png")
end

function leapfrog32(x::Float32,v::Float32,n::Int32,h::Float32)::Tuple{Float32,Float32}
    for i in 1:n
        xnew         = (x + h * v) + (h * h * - x) / 2f0
        vnew         = v + (h*(- x + - xnew)/2f0)
        x            = xnew
        v            = vnew
    end
    return (x,v)
end

function leapfrog64(x::Float64,v::Float64,n::Int64,h::Float64)::Tuple{Float64,Float64}
    for i in 1:n
        xnew         = (x + h * v) + (h * h * - x) / 2
        vnew         = v + (h*(- x + - xnew)/2)
        x            = xnew
        v            = vnew
    end
    return (x,v)
end

function plot_julia(sz)
    # choose random starting values in interval
    x1 = [Float64(rand(Uniform(-1,1))) for n in 1:sz]
    v1 = [Float64(rand(Uniform(-1,1))) for n in 1:sz]
    x2 = [Float32(x) for x in x1]
    v2 = [Float32(v) for v in v1]
    # define time step
    h32 = (1f0/32f0)
    h64 = 1/32
    # integrate
    LF32x = [leapfrog32(x2[i],v2[i],Int32(1),h32)[1] for i in 1:sz]
    LF64x = [leapfrog64(x1[i],v1[i],1,h64)[1] for i in 1:sz]
    # determine error
    xs   = [abs(LF32x[i] - LF64x[i]) for i in 1:sz]
    max1 = maximum(xs)

    plot([pbnd for i in 1:sz],seriestype="vline",label="formally proven bound=$pbnd" )
    plot!([max1 for i in 1:sz],seriestype="vline",label="worst empirical error=$max1" )
    plota = histogram!(xs, xlabel = "floating-point error",ylabel = "frequency",
    label="empirical error",size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
    legendfontsize=12, yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12)
    savefig(plota,fpath*"/julia_errors.png")

    plot([pbnd for i in -1:1],seriestype="hline",label="formally proven bound=$pbnd" )
    plotb = scatter!(x1,xs, ylabel = "floating-point error",xlabel = "position val",
    size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
    yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12, label="empirical error",
    xlims = (-1,1))
    savefig(plotb,fpath*"/julia_errors2.png")
end

function main(file1,file2,file3,file4,sz)
    """file1 should be a txt file containing 2n
    random inputs (n for position followed by n for velocity)

    file2 should be a txt file containing 2n
    outputs of m steps of integration
    (n for position followed by n for velocity)
    """

    plot_comps(file1,file2,file3,file4)
    plot_julia(sz)
    
end
