
####################################################################################################
#
# Envelope Cascade Implementation of the Bernoulli Factory, for Linear/Concave Functions
# 
#
####################################################################################################


#returns the tables necessary to get the a,b,c counts.
choose.wisely <- function (nn,kk,pp) {
  dd <- exp(sapply(kk,FUN=function(ii)
                   if ((ii>0)&(ii<nn)) sum(log(1:nn))-sum(log(1:ii))-sum(log(1:(nn-ii)))+ii*log(pp)+(nn-ii)*log(1-pp) else
                   ii*log(pp)+(nn-ii)*log(1-pp)))
  if (pp==0) dd <- c(1,rep(0,nn))
  if (pp==1) dd <- c(rep(0,nn),1)
  return(dd)
}

#two implementations of choose(nn,kk) in the log space since we leave standard double precision very quickly.
choose.gamma <- function(nn,kk,log=FALSE) {
  r1 <- sapply(kk,FUN=function(count) lgamma(nn+1) - lgamma(nn-count+1) - lgamma(count+1))
  if (!log) r1 <- exp(r1)
  return(r1)
}
choose.ints <- function(nn,kk,log=FALSE) {
  r1 <- rep(0, length(kk))
  if (any(kk!=0)) r1[kk!=0] <- sapply(kk[kk!=0], FUN=function(count)  sum(log((nn-count+1):nn),-log(1:count)))
  r1[kk==0] <- 0
  r1[kk<0] <- -Inf
  r1[kk>nn] <- -Inf
  if (!log) r1 <- exp(r1)
  return(r1)
}
choose.sensibly <- function(nn,kk,log=FALSE) {
  r1 <- log(choose(nn,kk))
  redo <- which(r1==Inf)
  if (!log) r1 <- exp(r1)
  r1[redo] <- choose.ints(nn, kk[redo], log)
  return(r1)
}


#Find the minimum of a quadratic-like function over an integer space. 
quadratic.integer.search <- function(fn, min.point, max.point, ...) {

  message(paste("QIS", min.point, max.point))
  retval <- NULL
  if (max.point-min.point < 10) {
    sequ <- seq(round(min.point),round(max.point))
    fn.eval <- sapply(sequ, fn, ...)
    retval <- which(fn.eval==min(fn.eval))[1]
  } else {
    ints <- ceiling((max.point-min.point)*0:4/4 + min.point)
    fn.eval <- sapply(ints, fn, ...)
    if (all(fn.eval==min(fn.eval))) retval <- ints[3] else 
    if (fn.eval[1]==min(fn.eval)) retval <- ints[1] else 
    if (fn.eval[5]==min(fn.eval)) retval <- ints[5] else 
    if (length(unique(fn.eval)) <= 3) retval <- ints[2] else 
    if (fn.eval[3]==min(fn.eval)) retval <- quadratic.integer.search(fn, ints[2], ints[4], ...) else
    if (fn.eval[2]==min(fn.eval)) retval <- quadratic.integer.search(fn, ints[1], ints[3], ...) else
    if (fn.eval[4]==min(fn.eval)) retval <- quadratic.integer.search(fn, ints[3], ints[5], ...)
  }
  return(retval)
}


upper.h.elbow <- function(pp, cons=list(cs=2, es=0.2)) pmin(cons$cs*pp,1-cons$es) #an upper envelope for the elbow function.
bernstein.polynomial <- function (x, func=upper.h.elbow, cons) #bernstein polynomial, bounded to 1. 
    sapply(x,FUN=function(ii) min(sum(func(0:cons$n/cons$n,cons)*choose.wisely(cons$n, 0:cons$n, ii)),1))
bernstein.polynomial.unbounded <- function (x, func=upper.h.elbow, cons) 
    sapply(x,FUN=function(ii) sum(func(0:cons$n/cons$n,cons)*choose.wisely(cons$n, 0:cons$n, ii)))


#Given an output terrace, simulate 10000 trials for the factory and estimate the expected value of the number of input bits.
ex.val <- function(output, pp=0.01, trials=10000) {
  o1 <- dberfac(pp, output$tables)
  nn <- as.numeric(colnames(o1))
  nn <- c(nn, 1000*nn[length(nn)]) #for now, make the number of draws for ``failure'' huge.
  surv <- o1[3,]
  probs <- c(1, surv)-c(surv,0)
  draws <- sample(nn, trials, prob=probs, replace=TRUE)
  if (any(draws==nn[length(nn)])) warning ("The empirical expected value includes rough estimates from empirically failed trials.")
  output.values <- cbind(c(mean(draws), sd(draws))); rownames(output.values) <- c("mean", "sd")
  return(output.values)
}


#What are the probabilities of each outcome at each n in the object, for input probability pp?
dberfac <- function(pp, terrace) {
  #terrace=stuff; pp=0.01; kk=1
  output <- sapply(1:length(terrace), function(kk) {
    prob.part <- (1:dim(terrace[[kk]])[1] - 1)*log(pp) +
      (dim(terrace[[kk]])[1]:1 - 1)*log(1-pp)
    totals <- exp(prob.part + terrace[[kk]][,1:3])
    apply(totals, 2, sum)
  })
  colnames(output) <- sapply(terrace, nrow)-1
  return(output)
}


#Given the input sequence of bits and the ``terrace'' collection of set sizes, return n.out output Bernoullis.
rberfac <- function(input,
                    n.out=1,
                    preamble=output.sets,
                    return.terrace=FALSE) {#start of rberfac.
  #preamble=stuff; input=rbinom(10000, 1, 0.01); n.out=100;return.terrace=FALSE
  terrace <- preamble$terrace
  
  p.est <- mean(input)
  stepsize <- dim(terrace[[2]])[1]-dim(terrace[[1]])[1]
  min.n <- dim(terrace[[1]])[1]-1
  curmax <- length(terrace)

  jimbo <- length(terrace)
  output <- NULL; bits.used <- NULL
  repeat {
    if (length(input)<min.n) break
    step <- 1
    tinp <- input[1:min.n]; input <- input[(min.n+1):length(input)]
    current.usage <- min.n

    kk <- sum(tinp); current.n <- length(tinp)
    drew <- terrace[[step]][kk+1,1:3]
    #message(paste(step, paste(drew, collapse=" ")))
    aset <- drew[1]; bset <- drew[2]; cset <- drew[3]
    mx <- max(aset,bset,cset)
    draw <- rbinom(1,1,exp(aset-mx)/(exp(aset-mx)+exp(bset-mx)+exp(cset-mx)))
    if (draw==0) {
      mx <- max(bset,cset)
      draw <- -rbinom(1,1,exp(cset-mx)/(exp(bset-mx)+exp(cset-mx))) #cset/(cset+bset))
    }

    if (draw>=0) {
      output <- c(output,draw)
      bits.used <- c(bits.used, current.usage)
    } else repeat {
      #if (length(input) < stepsize) break
      step <- step+1
      if (step>length(terrace)) stop (paste("rberfac went beyond the limits of the software. Input left:",length(input),
                                            "\nCurrent holding:",length(tinp),
                                            "\nCurrent outputs:",length(output),
                                            "\nOutput mean:", mean(output),
                                            "\nOnes and zeroes:", kk, current.n-kk,
                                            "\nTermination odds:", bset, cset, overdrew[2], overdrew[3]
                                            )) #terrace <- build.terrace(cons,stepsize,depth=step+3,p.est=p.est)
      stepsize <- dim(terrace[[step]])[1]-dim(terrace[[step-1]])[1]
      if (length(input) < stepsize) break
      
      tinp <- c(tinp,input[1:stepsize]); input <- input[(stepsize+1):length(input)]   #blocks of min.n in size.
      kk <- sum(tinp); current.n <- length(tinp)
      drew <- terrace[[step]][kk+1,4:6]
      overdrew <- terrace[[step]][kk+1,1:3]
      if (any(is.na(drew))) stop(paste("In stage",step,"NAs detected in the trinomial probabilities."))
      #message(paste(step, paste(drew, collapse=" ")))

      aset <- drew[1]; bset <- drew[2]; cset <- drew[3]
      
      mx <- max(aset,bset,cset)
      draw <- rbinom(1,1,exp(aset-mx)/(exp(aset-mx)+exp(bset-mx)+exp(cset-mx)))
      if (draw==0) {
        mx <- max(bset,cset)
        draw <- -rbinom(1,1,exp(cset-mx)/(exp(bset-mx)+exp(cset-mx))) #cset/(cset+bset))
      }
      #draw <- rbinom(1,1,aset/(aset+bset+cset)); if (draw==0) draw <- -rbinom(1,1,cset/(cset+bset))

      if (draw>=0) {
        output <- c(output,draw);
        bits.used <- c(bits.used, current.n)
        break
      }
      if (length(input)<min.n) break
    }

    if (length(input)<min.n) break
    if (length(output)>=n.out) break
  }

  #print(length(output))
  if (length(output)<n.out) warning("Ran out of input bits before requested number of outputs was reached.")
  
  out.list <- list(output=output, bits.used=bits.used, unused.input=input)
  if (return.terrace) out.list$terrace <- terrace
  return(out.list)
}



#Nice output of the cascade curves. General form.
plot.berfac.curves <-
  function(output,  #tables and constants
           
           function.form=output$function.form,  #factory.function.
           function.constants=output$function.constants,

           envelope.form=output$upper.function,
           
           descent.curve=output$descent.curve,  #x,y coordinates.
           pointcount=500,
           main="Bernoulli Factory Output",
           color.sequence=2:500,
           ...) {
  #pointcount=500; output=tryme.fhmod; function.form=output$function.form; function.constants=output$function.constants;  descent.curve=output$descent.curve; main="Bernoulli Factory Output"; envelope.form=output$upper.function
  
  plot(c(0,1), c(0,1), ty="n", main=main, xlab="p", ylab="f(p)", ...)
  if (!is.null(descent.curve)) lines(descent.curve, lty=3, lwd=2)
    
  xx <- 0:pointcount/pointcount
  target <- NULL
  if (!is.null(function.form)) {
    target <- function.form(xx, function.constants)
    lines (xx, target, col=1, lwd=8, lty=4)
  }
  out.yy <- sapply(xx, function(x.values) {
    dbf <- dberfac(x.values, output$tables)
    return(c(dbf[1,], 1-dbf[2,]) )
  })
  
  for (kk in 1:length(output$tables)) {
    nn <- dim(output$tables[[kk]])[1]-1; #print(nn)
    cons.parts <- output$constants[kk,-1]#); names(cons.parts) <- names(output$constants)[-1]
    lines (xx, envelope.form(xx, cons.parts), col=8)
    lines (xx, out.yy[kk,], col=color.sequence[kk], lty=2, lwd=2)
    lines (xx, out.yy[kk+length(output$tables),], col=color.sequence[kk], lty=2, lwd=2)
  }
  
  function.output <- list(xx=xx, yy=out.yy, target=target) 
  return(invisible(function.output))
}





###########################################################################
#
# Functions for specifying the envelopes.
#
###########################################################################


#complete one iteration of the factory to identify set sizes.
one.step <- function (lower.constants, upper.constants, lower.g, upper.h, ii=1, verbose=1) {
  
  current.n <- upper.constants$n
  #if (verbose) print(c(lower.constants, upper.constants))
  cs <- choose(current.n, 0:current.n)
  gs <- lower.g(0:current.n/current.n, lower.constants)
  hs <- upper.h(0:current.n/current.n, upper.constants$cons)
  
                                        #small fix there for machine precision.
  aa <- log(floor(cs*gs+1e-8)); bb <- log(floor(cs*(1-hs)+1e-8));
  mm <- pmax(log(cs), aa, bb);
  ccow <- mm + log(cs*exp(-mm)-exp(aa-mm)-exp(bb-mm))
  
  bad.subs <- which(is.infinite(aa)*(aa>0) | is.infinite(bb)*(bb>0) |
                    is.infinite(ccow)*(ccow>0) |
                    is.na(aa) | is.na(bb) |
                    is.na(ccow))
  if (length(bad.subs)>0) { #or problems here?
    message(paste("Invalid standard calculations in repetition",ii,". Reverting to integer form for choose function."))
    cs <- choose.ints(current.n, (0:current.n)[bad.subs], log=TRUE)
    aa[bad.subs] <- cs+log(gs[bad.subs]); bb[bad.subs] <- cs+log(1-hs[bad.subs]);
    mm <- pmax(cs, aa[bad.subs], bb[bad.subs]); ccow[bad.subs] <- mm + log(exp(cs-mm)-exp(aa[bad.subs]-mm)-exp(bb[bad.subs]-mm))
  }
  output <- cbind(aa, bb, ccow); colnames(output) <- c("a","b","c")
  return(output)
}

#subtract those set elements that would have been picked in previous iterations.
remove.previous.draws <- function (current.set, previous.set) {
  non <- dim(previous.set)[1]-1
  stoop <- dim(current.set)[1]-dim(previous.set)[1]
  stiff <- rbind(previous.set[,1:3], array(-Inf,c(stoop,3)))

  current.n <- dim(current.set)[1]-1
  
  newn <- non+stoop
  
  o2 <- current.set
  for (kk in 0:newn) {
                                        #kk<-kk+1
                                        #gather all for A_{n,k}.
    precount <- choose.sensibly(stoop, 0:stoop, log=TRUE)
    a.hold <- -Inf
                                        #jj <- 0
    
    for (jj in 0:min(stoop,kk)) {
                                        #message(paste("a",stiff[kk-jj+1,1], precount[jj+1], stiff[kk-jj+1,1]+precount[jj+1], jj, kk))
      mx <- max(a.hold, stiff[kk-jj+1,1]+precount[jj+1])
      if (mx > -Inf) a.hold <- mx+log(exp(a.hold-mx)+exp(stiff[kk-jj+1,1]+precount[jj+1]-mx))
    }
                                        #subtract the sum total.
                                        #message(paste("+a",a.hold,"+",o2[kk+1,1]))
    if (a.hold > o2[kk+1,1]) {warning(paste("Floating point error? a.hold>o2[kk,1], kk=", kk,"nn=",current.n, a.hold, o2[kk+1,1], a.hold-o2[kk+1,1])); a.hold <- o2[kk+1,1]} 
    mx <- max(o2[kk+1,1], a.hold)
    if (mx > -Inf) o2[kk+1,1] <- mx + log(exp(o2[kk+1,1]-mx) - exp(a.hold-mx))
    
    b.hold <- -Inf
    for (jj in 0:min(stoop,kk)) {
                                        #message(paste("b",stiff[kk-jj+1,1], precount[jj+1], stiff[kk-jj+1,1]+precount[jj+1], jj, kk))
      mx <- max(b.hold, stiff[kk-jj+1,2]+precount[jj+1])
      if (mx > -Inf) b.hold <- mx+log(exp(b.hold-mx)+exp(stiff[kk-jj+1,2]+precount[jj+1]-mx))
    }
                                        #subtract the sum total.
                                        #message(paste("+b",b.hold,"+",o2[kk+1,1]))
    if (b.hold > o2[kk+1,2]) {warning(paste("Floating point error? b.hold>o2[kk,1], kk=", kk,"nn=",current.n, b.hold, o2[kk+1,1], b.hold-o2[kk+1,1])); b.hold <- o2[kk+1,1]} 
    mx <- max(o2[kk+1,2], b.hold)
    if (mx > -Inf) o2[kk+1,2] <- mx + log(exp(o2[kk+1,2]-mx) - exp(b.hold-mx))
  }
  
  current.set <- cbind(current.set, o2)
  return(current.set)
}

#General form of set construction.
berfac.preamble.general <-
  function (factory.function=function(pp, cons) cons[1]+(1-cons[1])*pp^(1/cons[2]),
            target.cons=c(0,2),
            sequence.cons=cbind(c(0.5,0.3,0.1), c(10,4,3)),
            nn.sequence=c(100,200,300),
            upper.h=factory.function,
            verbose=TRUE) {#start of preamble.

  #factory.function=function(pp, cons) cons[1]+(1-cons[1])*pp^(1/cons[2]); target.cons=c(0,2); sequence.cons=cbind(c(0.5,0.3,0.1), c(10,4,3)); nn.sequence=c(100,200,300); upper.h=factory.function;  verbose=TRUE
  #source("rberfac-public-2.R")
  
  lower.g <- factory.function
  lower.constants <- target.cons
  output.sets <- list()
  upper.constant.set <- cbind (nn.sequence, sequence.cons)
  for (ii in 1:length(nn.sequence)) {
    upper.constants <- list(n=upper.constant.set[ii,1],
                            cons=upper.constant.set[ii,-1])
    output.sets[[ii]] <- one.step(lower.constants, upper.constants, lower.g, upper.h, ii)
    if (ii>1) output.sets[[ii]] <- remove.previous.draws (output.sets[[ii]], output.sets[[ii-1]])
  }

  set.sizes <- sapply(output.sets, nrow)-1
  message(paste("Number of steps:", length(output.sets), ", sizes", paste(set.sizes,collapse=":")))
  output <- list(tables=output.sets,
                 constants=upper.constant.set,
                 upper.function=upper.h,
                 
                 function.form=lower.g,
                 function.constants=lower.constants,

                 descent.curve=NULL)
  plotting.is.on <- FALSE
  if (plotting.is.on) plot.berfac.curves(output, pointcount=500)   
  return(output)
}

test.berfac.preamble.general <- function() {
  source("rberfac-public-2.R")

  tryme.zero <- berfac.preamble.general ()

  
  tryme <- berfac.preamble.general (sequence.cons=cbind(c(0,0,0), c(5,3,2.02)))
  pdf("bf-sqrt-cascade.pdf", width=6, height=6)
  plot.berfac.curves(tryme, pointcount=500, main="Bernoulli Factory: f(p)=sqrt(p)")
  dev.off()
  
  dberfac(0.01, tryme$tables)



  
  #linear 
  tryme.two <-
    berfac.preamble.general (upper.h=function(pp, cons) pmin(cons[1]+cons[2]*pp, 1),
                             sequence.cons=cbind(c(0.358),
                               c(0.7)),
                             nn.sequence=c(50))
  dberfac(0.5, tryme.two$tables)

  
  pdf("bf-sqrt-tangent.pdf", width=6, height=6)
  line.out <- plot.berfac.curves(tryme.two, pointcount=500, main="Bernoulli Factory: f(p)=sqrt(p)")
  dev.off()


  line.out$yy[6,]-line.out$target                                      
  
  ex.val(tryme.two, pp=0.5)
  
}



test.berfac.flegal.herbei.modified <- function() {
  source("rberfac-public-2.R")

  erfish <- function(x) (2*pnorm(x*sqrt(2))-1)*sqrt(pi)/2
  ffp <- function(x, cons) cons[3]*erfish(cons[1]*x/cons[3])
  #cons: a, omega, delta
  fhmod <- function(pp, cons=c(2,0.2,0.1)) (pp<((1-cons[2])/cons[1]))*(cons[1]*pp) +
    (pp>=((1-cons[2])/cons[1]))*((1-cons[2])+ffp((pp - (1-cons[2])/cons[1]), cons))
  CC <- function(cons) cons[1]^2*sqrt(2/exp(1))/cons[3]
  
  #xx <- seq(0,1,length=101); yy <- fhmod(xx); plot(xx, yy, xlim=c(0.2,0.7), ylim=c(0.5,0.96)); abline(h=0.9, col=2); abline(a=0,b=2,col=2); yy[-1]-yy[-101]
  
  tryme.fh <- berfac.preamble.general (factory.function=function(pp, cons) fhmod(pp, cons),
                                          target.cons=c(2,0.2,1/6),
                                          upper.h=function(pp, cons) fhmod(pp, cons)+CC(cons)/2/cons[4],
                                          
                                          sequence.cons=cbind(c(2,2,2),
                                            c(0.2,0.2,0.2),
                                            c(1/6,1/6,1/6),
                                            c(256,512,1024)),
                                          nn.sequence=c(256,512,1024))
  #note: floating point errors in "a" set can be expected due to the size of the sets.

  pdf("fh-original.pdf", width=6, height=6)
  plot.berfac.curves(tryme.fh, pointcount=1000, main="Bernoulli Factory: Flegal-Herbei Elbow")
  dev.off()
  pdf("fh-original-zoom.pdf", width=6, height=6)
  plot.berfac.curves(tryme.fh, pointcount=1000, main="Bernoulli Factory: Flegal-Herbei Elbow", xlim=c(0,0.2), ylim=c(0,0.2))
  dev.off()
  
  dberfac(0.01, tryme.fh$tables)
  
  tryme.fhmod <- berfac.preamble.general (factory.function=function(pp, cons) fhmod(pp, cons),
                                          target.cons=c(2,0.2,1/6),
                                          upper.h=function(pp, cons) fhmod(pp, cons)*(1+CC(cons)/2/cons[4]),
                                          
                                          sequence.cons=cbind(c(2,2,2),
                                            c(0.2,0.2,0.2),
                                            c(1/6,1/6,1/6),
                                            c(256,512,1024)),
                                          nn.sequence=c(256,512,1024))
  
  pdf("fh-adapted.pdf", width=6, height=6)
  plot.berfac.curves(tryme.fhmod, pointcount=1000, main="Bernoulli Factory: Flegal-Herbei Modified", xlim=c(0,0.2), ylim=c(0,0.2))
  dev.off()

  
  dberfac(0.01, tryme.fhmod$tables)
  
  tryme.fhsupermod <- berfac.preamble.general (factory.function=function(pp, cons) fhmod(pp, cons),
                                          target.cons=c(2,0.2,1/6),
                                          upper.h=function(pp, cons) fhmod(pp, cons)*(1+CC(cons)/2/cons[4]),
                                          
                                          sequence.cons=cbind(c(3,2,2,2),
                                            c(0.1,0.2,0.2,0.2),
                                            c(0.097,1/6,1/6,1/6),
                                            c(20000,256,512,1024)),
                                          nn.sequence=c(20,256,512,1024))
  
  pdf("fh-superadapted.pdf", width=6, height=6)
  plot.berfac.curves(tryme.fhsupermod, pointcount=1000, main="Bernoulli Factory: Flegal-Herbei Modified", color.sequence=c(5,2,3,4)) #, xlim=c(0,0.2), ylim=c(0,0.2))
  dev.off()
  pdf("fh-superadapted-zoom.pdf", width=6, height=6)
  plot.berfac.curves(tryme.fhsupermod, pointcount=1000, main="Bernoulli Factory: Flegal-Herbei Modified", color.sequence=c(5,2,3,4), xlim=c(0,0.2), ylim=c(0,0.2))
  dev.off()

  dberfac(0.01, tryme.fhsupermod$tables)
  
}





#do a demo for a square root. By hand.
berfac.preamble.root <- function (root.power=2,
                                  nn.sequence=c(100,200,300),
                                  rise.sequence=c(0.5,0.3,0.1),
                                  root.sequence=c(10,4,3),
                                  verbose=TRUE) {#start of preamble.

  #Diagnostic values.
  #root.power=2; nn.sequence=c(100,200,300,400,1000); rise.sequence=c(0.5,0.3,0.1,0,0); root.sequence=c(10,4,3,2.2,2.01); verbose=TRUE
  #source("rberfac-public-2.R")
  
  factory.function <- function(pp, rise, root) rise+(1-rise)*pp^(1/root) 
  upper.h <- lower.g <- function(p, cons) factory.function(p, cons$rise, cons$root) #upper envelope
  
  lower.constants <- list(rise=0,
                     root=root.power,
                     n=nn.sequence[1])
    
  output.sets <- list()
  upper.constant.set <- cbind (nn.sequence, rise.sequence, root.sequence)

  for (ii in 1:length(nn.sequence)) {
    upper.constants <- list(n=upper.constant.set[ii,1],
                            cons=list(rise=upper.constant.set[ii,2], root=upper.constant.set[ii,3]))
    output.sets[[ii]] <- one.step(lower.constants, upper.constants, lower.g, upper.h, ii)
    if (ii>1) output.sets[[ii]] <- remove.previous.draws (output.sets[[ii]], output.sets[[ii-1]])
  }

  set.sizes <- sapply(output.sets, nrow)-1
  
  message(paste("Number of steps:", length(output.sets), ", sizes", paste(set.sizes,collapse=":")))
  
  output <- list(tables=output.sets,
                 constants=data.frame(upper.constant.set),
                 function.form=upper.h,
                 
                 upper.function=upper.h,
                 function.constants=lower.constants,
                 descent.curve=NULL)

  plotting.is.on <- FALSE
  if (plotting.is.on) plot.berfac.curves(output,
                                         pointcount=500) 
  
  return(output)
 
}

test.berfac.preamble.root <- function() {
  source("rberfac-public-2.R")
  tryme <- berfac.preamble.root (root.power=2,
                                 nn.sequence=c(100,200,300,400),
                                 rise.sequence=c(0.5,0.3,0.1,0),
                                 root.sequence=c(10, 4, 3, 2.2),
                                 verbose=TRUE)
  plot.berfac.curves(tryme, pointcount=500)
  dberfac(0.01, tryme$tables)
  ex.val(tryme)

}





#This is where the hard labor actually happens. Once these tables are defined, rberfac just makes use of them rather than recalculating each time.
berfac.preamble.elbow <-
  function (multiplier,
            ep,
            initial.n=50,
            initial.elbow.y=(1-ep/5),
            elbow.power=5,
            
            step=100,

            decrease.proportion=1/4,
            total.terrace.size=8,
            last.iteration.nn.boost=1000,
            verbose=TRUE) {#start of preamble.

  #Diagnostic values.
  #multiplier=2; ep=0.2; initial.n=20; initial.elbow.y=0.985; step=20; total.terrace.size=3; last.iteration.nn.boost=100; verbose=TRUE; elbow.power=5; decrease.proportion=1/2;
  #prepare the counts.

  if (initial.elbow.y < 1-ep) stop("Invalid initial envelope placement.")
  
  factory.function <- lower.g <- upper.h <- function(p, cons) pmin(cons$cs*p,1-cons$es) 

  upper.constants <- NULL
  lower.constants <- list(cs=multiplier, es=ep, n=initial.n)
  
  #descent curve, form-fit to small p.
  descent.x <- function(yy, pow=elbow.power, epsilon=ep, mult=multiplier) -((yy-(1-epsilon))/epsilon)^pow/multiplier + yy/multiplier
  
  f.to.min <- function(yy) abs(bernstein.polynomial(descent.x(yy), upper.h, upper.constants)-yy)
  elbow.x <- elbow.y <- envelope.ep <- envelope.ml <- rep(NA, total.terrace.size+1)
  elbow.y[1] <- initial.elbow.y; elbow.x[1] <- descent.x(elbow.y[1])
  envelope.ep[1] <- 1-elbow.y[1]; envelope.ml[1] <- elbow.y[1]/elbow.x[1]
  
  message (paste("Initial elbow point:", elbow.x[1], elbow.y[1], ep, step, initial.n))
  xcrit <- (1-ep)/multiplier  #critical value of x.
  ycrit <- (1-ep)

  output.sets <- NULL
  constants <- NULL
  current.n <- initial.n - step
  
  ii <- 0
  redo.count <- 0
  iq <- 0.05
      
  repeat {
    ii <- ii+1

    upper.constants$es <- envelope.ep[ii] <- 1-elbow.y[ii];
    upper.constants$cs <- envelope.ml[ii] <- elbow.y[ii]/elbow.x[ii];
    current.n <- current.n+step;
    upper.constants$n <- current.n
    
    point.checks <- 200
    if (ii==1) {
  
      if ((bernstein.polynomial(xcrit, upper.h, upper.constants)-ycrit<0)) {
        message (paste("For",ii,"the upper envelope cut the objective function:",
                       bernstein.polynomial(xcrit, upper.h, upper.constants), ycrit,
                       " -- redoing previous step with more input bits."))
        redo.count <- redo.count+1
        ii <- ii - redo.count
        upper.constants$es <- envelope.ep[ii] <- 1-elbow.y[ii];
        upper.constants$cs <- envelope.ml[ii] <- elbow.y[ii]/elbow.x[ii];
      }
    } else {
        #new criteria: pick current.n so that the gap from the curve is cut by a fixed proportion.
      current.n <- dim(output.sets[[ii-1]])[1]-1
      
      p1 <- bernstein.polynomial(xcrit, upper.h, cons=list(n=dim(output.sets[[ii-1]])[1]-1,
                                                   es=envelope.ep[ii-1],
                                                   cs=envelope.ml[ii-1]))
      bpn <- function(nn) bernstein.polynomial(xcrit, upper.h, cons=list(n=trunc(nn),
                                                                 es=envelope.ep[ii],
                                                                 cs=envelope.ml[ii]))
      
      test.fn <- function(chk) (chk-(decrease.proportion*ycrit+(1-decrease.proportion)*p1))^2

      first.check <- bpn(current.n)
      second.check <- bpn(current.n+1)
      if (first.check < ycrit | test.fn(second.check) > test.fn(first.check)) { ## no progress.
        ex1 <- elbow.x[ii]; ey1 <- elbow.y[ii]
        while ((bernstein.polynomial(elbow.x[ii], upper.h, upper.constants)-(1-ep))/
               abs(ep-(1-elbow.y[ii-1])) > 1-decrease.proportion) {
          ex1 <- elbow.x[ii]; ey1 <- elbow.y[ii]
          
          elbow.y[ii] <- (iq*elbow.y[ii]+ycrit)/(iq+1); elbow.x[ii] <- descent.x(elbow.y[ii])
          upper.constants$es <- 1-elbow.y[ii]; upper.constants$cs <- elbow.y[ii]/elbow.x[ii]
        }
      
        elbow.x[ii] <- ex1;
        elbow.y[ii] <- ey1;
        upper.constants$es <- envelope.ep[ii] <- 1-elbow.y[ii]; 
        upper.constants$cs <- envelope.ml[ii] <- elbow.y[ii]/elbow.x[ii]
      }

      
      temp.point.checks <- point.checks; pick <- NULL; if (ii<total.terrace.size) while (length(pick)==0) {
        first.check <- bpn(current.n+(temp.point.checks-1))
        second.check <- bpn(current.n+(temp.point.checks-2))
        if (first.check < ycrit | test.fn(second.check) > test.fn(first.check)) {
          current.n <- current.n+temp.point.checks
          temp.point.checks <- temp.point.checks + point.checks
          message(paste("Minimum current.n:", current.n, ";", first.check, ycrit, p1))
        } else {
          current.n <- quadratic.integer.search(test.fn, current.n+step, current.n+temp.point.checks)
          pick <- current.n         
        }
      }
      upper.constants$n <- current.n
    }



    #If this is the last round for now, push it to the limit.
    if (ii==total.terrace.size) { #milk what we can out of it!
      message(paste("Reached",ii,", the last terrace."))
      
      current.n <- current.n + last.iteration.nn.boost
      upper.constants$n <- current.n
      ex1 <- elbow.x[ii]; ey1 <- elbow.y[ii]

      #new goal: seek the point where bf(elbow)=1-ep+1e-5).
      f.int <- function(yy) {
        xx <- descent.x(yy)
        cons <- list(es=1-yy, cs=yy/xx, n=current.n)
        return((bernstein.polynomial(xcrit, upper.h, cons)-(1-ep+1e-5))^2)
      }
      message("Optimizing final placement")
      test <- optimize(f.int, c(ey1, 1-ep))
                       #obj <- optimize(f.to.min, c(elbow.y[ii],1-ep))
      elbow.y[ii] <- test$min; elbow.x[ii] <- descent.x(elbow.y[ii])
      message(paste("Optimized final placement.", elbow.y[ii], elbow.x[ii]))

      upper.constants$es <- envelope.ep[ii] <- 1-elbow.y[ii];
      upper.constants$cs <- envelope.ml[ii] <- elbow.y[ii]/elbow.x[ii]
      
    }
    lower.constants$n = current.n


    output.sets[[ii]] <- one.step(lower.constants, list(n=upper.constants$n, cons=upper.constants), lower.g, upper.h, ii)
    if (ii>1) output.sets[[ii]] <- remove.previous.draws (output.sets[[ii]], output.sets[[ii-1]])

    obj <- optimize(f.to.min, c(elbow.y[ii],1-ep))

    #set the next point.
    elbow.y[ii+1] <- obj$min; elbow.x[ii+1] <- descent.x(elbow.y[ii+1])
    if (verbose) message(paste("Done:",ii,", bits=", nrow(output.sets[[ii]])-1))
    constants <- rbind(constants, c(upper.constants$n, upper.constants$cs, upper.constants$es))
    
    if (ii >= total.terrace.size) break

  }
  
  colnames(constants) <- c("n","cs","es")
  set.sizes <- sapply(output.sets, nrow)
  
  message(paste("Number of steps:", length(output.sets), ", sizes", paste(set.sizes,collapse=":")))

  descent.yyy <- seq(1, 1-ep, length=100)
  output <- list(tables=output.sets,
                 constants=data.frame(constants),
                 upper.function=upper.h,

                 function.form=upper.h,
                 function.constants=lower.constants,
                 descent.curve=cbind(descent.x(descent.yyy, pow=elbow.power, epsilon=ep, mult=multiplier), descent.yyy))

  plotting.is.on <- FALSE
  if (plotting.is.on) plot.berfac.curves(output,
                                         pointcount=500) 
  
  return(output)
}

test.berfac.preamble.elbow <- function () {
  source("rberfac-public-2.R")
  tryme <- berfac.preamble.elbow (2, 0.2, step=100, last.iteration=500, total.terrace.size=4)
  names(tryme)
  plot.berfac.curves(tryme, pointcount=500)
  dberfac(0.01, tryme$tables)
  ex.val(tryme)
}




#do a demo for a parabola:
#para <- function(pp, top=0.5) top-4*top*(pp-0.5)^2
berfac.preamble.parabola <- function (top,
                                      initial.n=50,
                                      initial.y.top=(1-(1-top)/5),
                                      step=500,
                                      decrease.proportion=1/4,
                                      total.terrace.size=8,
                                      last.iteration.nn.boost=1000,
                                      verbose=TRUE,
                                      slam.comfort=1e-5) {#start of preamble.

  #Diagnostic values.
  #top=0.8; initial.n=20; initial.y.top=0.985; step=20; total.terrace.size=3; last.iteration.nn.boost=100; verbose=TRUE; decrease.proportion=1/2;
  #prepare the counts.

  if (initial.y.top < top) stop("Invalid initial envelope placement.")
  
  lower.g <- upper.h <- factory.function <- function(pp, cons) cons$top-4*cons$top*(pp-0.5)^2
  
  upper.constants <- NULL
  lower.constants <- list(top=top, n=initial.n)
  
  #descent curve, form-fit to small p.
  descent.x <- function(yy) rep(0.5, length(yy)) #-((yy-(1-epsilon))/epsilon)^pow/multiplier + yy/multiplier
  
  f.to.min <- function(yy) abs(bernstein.polynomial(descent.x(yy), upper.h, upper.constants)-yy)
  elbow.y <- elbow.x <- rep(NA, total.terrace.size+1)   #envelope.ep <- envelope.ml <- 
  elbow.y[1] <- initial.y.top; elbow.x[1] <- 0.5
  
  
  message (paste("Initial elbow point:", elbow.y[1]))
  #xcrit <- (1-ep)/multiplier      #critical value of x.
  xcrit <- 0.5
  ycrit <- top
  
  output.sets <- NULL
  current.n <- initial.n-1
  ii <- 0
  redo.count <- 0
  iq <- 0.05
  constants <- NULL
  
  repeat {
    ii <- ii+1

    upper.constants$top <- elbow.y[ii];
    current.n <- current.n+1; upper.constants$n <- current.n
    
    point.checks <- 200
    if (ii==1) {
  
      if ((bernstein.polynomial(xcrit, upper.h, upper.constants)-ycrit<0)) {
        message (paste("For",ii,"the upper envelope cut the objective function:",
                       bernstein.polynomial(xcrit, upper.h, upper.constants), ycrit,
                       " -- redoing previous step with more input bits."))
        redo.count <- redo.count+1
        ii <- ii - redo.count
        upper.constants$top <- elbow.y[ii];
      }
      
    } else {
        #new criteria: pick current.n so that the gap from the curve is cut by a fixed proportion.
      current.n <- dim(output.sets[[ii-1]])[1]
      
      p1 <- bernstein.polynomial(xcrit, upper.h, cons=list(n=dim(output.sets[[ii-1]])[1]-1,
                                                   top=elbow.y[ii-1]))
      bpn <- function(nn) bernstein.polynomial(xcrit, upper.h, cons=list(n=trunc(nn),
                                                                 top=elbow.y[ii-1]))
      
      test.fn <- function(chk) (chk-(decrease.proportion*ycrit+(1-decrease.proportion)*p1))^2

      first.check <- bpn(current.n)
      second.check <- bpn(current.n+1)
      if (first.check < ycrit | test.fn(second.check) > test.fn(first.check)) { ## no progress.
        ex1 <- elbow.x[ii]; ey1 <- elbow.y[ii]
        while ((bernstein.polynomial(elbow.x[ii], upper.h, upper.constants)-top)/abs(1-top-(1-elbow.y[ii-1])) > 1-decrease.proportion) {
          ex1 <- elbow.x[ii]; ey1 <- elbow.y[ii]
          
          elbow.y[ii] <- (iq*elbow.y[ii]+ycrit)/(iq+1); elbow.x[ii] <- descent.x(elbow.y[ii])
          upper.constants$top <- elbow.y[ii]; 
        }
      
        elbow.x[ii] <- ex1;
        elbow.y[ii] <- ey1;
        upper.constants$top <- elbow.y[ii]; 
      }

      
      temp.point.checks <- point.checks; pick <- NULL; while (length(pick)==0) {
        first.check <- bpn(current.n+(temp.point.checks-1))
        second.check <- bpn(current.n+(temp.point.checks-2))
        if (first.check < ycrit | test.fn(second.check) > test.fn(first.check)) {
          current.n <- current.n + temp.point.checks
          temp.point.checks <- temp.point.checks + point.checks
          message(paste("Minimum current.n:", current.n, ";", first.check, ycrit, p1))
        } else {
          current.n <- quadratic.integer.search(test.fn, current.n, current.n+temp.point.checks)
          pick <- current.n         
        }
      }
      
      upper.constants$n <- current.n
      
    }



    #If this is the last round for now, push it to the limit.
    if (ii==total.terrace.size) { #milk what we can out of it!
      message(paste("Reached",ii,", the last terrace."))
      
      current.n <- current.n + last.iteration.nn.boost
      upper.constants$n <- current.n
      ex1 <- elbow.x[ii]; ey1 <- elbow.y[ii]

      #new goal: seek the point where bf(elbow)=1-ep+1e-5).
      f.int <- function(yy) {
        xx <- descent.x(yy)
        cons <- list(top=yy, n=current.n)
        return((bernstein.polynomial(xcrit, upper.h, upper.constants)-(top+slam.comfort))^2)
      }
      message("Optimizing final placement")
      test <- optimize(f.int, c(ey1, top))
                       #obj <- optimize(f.to.min, c(elbow.y[ii],1-ep))
      elbow.y[ii] <- test$min; elbow.x[ii] <- descent.x(elbow.y[ii])
      message(paste("Optimized final placement.", elbow.y[ii], elbow.x[ii]))

     upper.constants <- list(top=elbow.y[ii], n=current.n)
      
    }
    lower.constants$n = current.n

    
    output.sets[[ii]] <- one.step(lower.constants, list(n=upper.constants$n, cons=upper.constants), lower.g, upper.h, ii)
    if (ii>1) output.sets[[ii]] <- remove.previous.draws (output.sets[[ii]], output.sets[[ii-1]])

    
    obj <- optimize(f.to.min, c(elbow.y[ii], top))

    #set the next point.
    elbow.y[ii+1] <- obj$min; elbow.x[ii+1] <- descent.x(elbow.y[ii+1])
    
    if (verbose) message(paste("Done:",ii,", bits=",nrow(output.sets[[ii]])-1))

    constants <- rbind(constants, c(upper.constants$n, upper.constants$top))
    
    if (ii >= total.terrace.size) break
  }
  set.sizes <- sapply(output.sets, nrow)
  colnames(constants) <- c("n","top")
  
  message(paste("Number of steps:", length(output.sets), ", sizes", paste(set.sizes,collapse=":")))

  output <- list(tables=output.sets,
                 constants=data.frame(constants),
                 upper.function=upper.h,

                 function.form=upper.h,
                 function.constants=lower.constants)


  return(output)
 
}

test.berfac.preamble.parabola <- function () {
  source("rberfac-public-2.R")

  parab <- berfac.preamble.parabola(top=0.5, initial.n=10,
                           step=20, total=4, decrease.proportion=3/4,
                           last=1000, initial.y.top=0.7)
  names(parab)

  plot.berfac.curves(parab, pointcount=500)
  dberfac(0.01, tryme$tables)
  ex.val(tryme)
}

