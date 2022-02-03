# PLANN-model-for-ndhs-data
library(survival)
library(pec)
library(caret)
library(RColorBrewer)
library(wesanderson)
library(haven)
library(ggsci)
library(viridis)
library(e1071)
library(doParallel)
library ( survminer )
library(pcaPP)
library(rainbow)
library (rms)
library ( ggplot2 )
library ( grid )
library ( gridExtra )
library (pec )
library ( forestmodel )
library(MASS)
library(prodlim)
library(nnet)
library("neuralnet")
library(NeuralNetTools)
library(devtools)
library(coxed)
library(MatrixModels)
options(repos = c(CRAN = "http://cran.rstudio.com"))
par(mar=c(1,1,1,1))
setwd("C:/Users/OBITE C. P/Desktop/Survival data")
library(readxl)
data<- read_sav("C:/Users/OBITE C. P/Desktop/Project/project/marriage main4 gladys (3).sav")
data<-as.data.frame(data)
mean_data<-apply(data, 2, mean)
sd_data<-apply(data, 2, sd)
Cohabitation<-scale(data[,3], center = mean_data[3], scale = sd_data[3])
data2<-data$age_cohabitation
data2<-as.data.frame(data2)
data2<-scale(data2)
data1<-data[,c(1,2,4,5,6,7,8)]
status<- data$status
time <- data$time
Circumcision<- data$Circumcision
Region<- data$Region
Residence<- data$Residence
Religion<- data$Religion
Education<- data$Education
data_scaled1<-cbind(status,time,data2,Circumcision,Region,
                    Residence,Religion,Education)
data_scaled<-cbind(data1,data2)
data_scaled<-as.data.frame(data_scaled)
set.seed (1245)
N <- nrow (data)
index <- sample (1:N, round (N/3), replace = FALSE )


#Neural network
c1<-makeCluster(3)
registerDoParallel(c1)
id<-seq(1, nrow(data_scaled),1)
data_scaled<-cbind(data_scaled,id)
data_scaled<-data_scaled[order(data_scaled$id),]
# defining validation set and training set
#with equal proportions of events

one.set<- which(data_scaled$status==2)
zero.set<-which(data_scaled$status==1)
set.seed (1245)
ind.ones<-sample(one.set, length(one.set)/3, replace = FALSE)
set.seed (1245)
ind.zeros<-sample(zero.set, length(zero.set)/3, replace = FALSE)
validation.set.ind<-c(ind.ones,ind.zeros)
training.set.ind<-c(-ind.ones,-ind.zeros)
set.seed (1245)
N <- nrow (data)
index <- sample (1:N, round (N/3), replace = FALSE )
training_data<- data_scaled[-index,]
test_data<- data_scaled[index,]
cox.train<-data[-index,]
cox.test<-data[index,]


#transform the training data into long format
data_train<-function(data){
  set.seed (1245)
  N<-nrow(data)
  data$interval<-as.numeric(cut(data$time, breaks = 12))
  data$survival<-as.numeric(cut(data$time,breaks = 12))
  data$id<-1:N
  n.times<-data$interval
  data_long<-data[rep(seq_len(N), times = n.times),]
  
  #create the correct intervals
  for (i in unique(data_long$id)) {
    n_length<-length(data_long$interval[data_long$id == i])
    data_long$interval[data_long$id == i] <- 1:n_length
  }
  data_long$stat<-vector(mode = "numeric", length = nrow(data_long))
  #put indication 1 on status at the interval that patient dies
  for (i in 1:nrow(data_long)) {
    if (data_long$status[i] == 1 &&
        data_long$survival[i] <= data_long$interval[i])
      data_long$stat[i]<-1
  }
  return(data_long)
}

# function that creates data in the right long format for
# test set for each patient the interval 
# goes from 1 year till 12 years

data_test<-function(data){
  set.seed (1245)
  N<-nrow(data)
  #assign survival times to 12 intervals
  data$interval<-max(as.numeric(cut(data$time, breaks = 12)))
  # the true interval survival
  data$survival<-as.numeric(cut(data$time,breaks = 12))
  data$id<-70001:(70000+N) # define the patient ids abstractly
  n.times<-data$interval
  data_long<-data[rep(seq_len(N), times = n.times),]
  # create the correct intervals
  for (i in unique(data_long$id)) {
    n_length<-length(data_long$interval[data_long$id == i])  
    data_long$interval[data_long$id == i] <- 1: n_length
  }
  data_long$stat<-vector(mode = "numeric", length = nrow(data_long))
  #put indication 1 on status at the intervals on which a patient has died
  for (i in 1:nrow(data_long)) {
    if (data_long$status[i] == 1 &&
        data_long$survival[i] <= data_long$interval[i])
      data_long$stat[i]<-1
  }
  return(data_long)
}

# function to calculate Brier and Integrated Brier scores for ANN
brier_function.neur<-function(surv.preds, preds){
  # calculating censoring distribution
  so<- Surv(surv.preds$surv, surv.preds$stat)
  time<- so[,1]
  ot<- order(time)
  cens<- so[ot,2]
  time<-time[ot]
  N<- nrow(so)
  hatcdist<- prodlim(Surv(time,cens)~1,reverse = TRUE)
  #censoring weights (reverse Kaplan-Meier)
  csurv<-predict(hatcdist, times=time, type = "surv")
  csurv[csurv==0]<-Inf #access infinite value to censored
  btime<-time
  # matrix transpose of survival predictions
  survs<- t(preds)
  btime.n<-unique(time) #find the unique times
  bsc<- rep(0, length(btime.n))
  bsk<- rep(0, length(btime.n))
  
  for (j in 1:length(btime.n)){
    #indicator vectors for selecting relevant patients
    #the censored ones
    #help1 selects those individuals that have an event
    #at or before the time of interest. The predictions for 
    # these observations are compared
    
    help1<-as.integer(time<= btime.n[j] & cens == 1)
    help2<-as.integer(time>btime.n[j])
    
    # As the log of zero cannot be taken, values of 1 and 0
    # need to be modified: values of 1 are lowered by
    # 0.000001, values of 0 increased.
    inb <- survs[j,]
    inb[which(inb == 1)] <-(inb[which(inb == 1)]- 0.000001)
    inb[which(inb == 0)] <-(inb[which(inb == 0)]+ 0.000001)
    # Calculating brier scores for each unique time j, weighted by
    # the censoring distribution csurv
    
    bsc[j]<- mean((0 - survs[j,])^2 * help1 * (1/csurv) + (1-survs[j,])^2 * help2 * (1/csurv[j]))
    # calculating KL scores for each unique time j, weighted
    # by the censoring distribution csurv. surv[j,] has been
    #replaced by inb (defined above) to solve the problem of
    #extreme predictions.
    bsk[j]<- -mean((log(1-(inb))* help1*(1/csurv) + log(inb)*(1/csurv[j])*help2))
  }
  ind.values<-seq(1,4)
  rel.vals<- vector("numeric", length(ind.values))
  for (i in 1:length(ind.values)) {
    rel.vals[[i]]<-which.min(abs(btime-ind.values[i]))
  }
  Brie <- bsc[rel.vals]
  KL<- bsk[rel.vals]
  RET<- rbind(Brie,KL)
  return(RET)
}

# Brier/KL score function slightly modified to suit Cox
brier_nnet.cox.m<-function(imp, preds){
  # calculating censoring distribution
  so<- Surv(imp$surv, imp$stat)
  time<- so[,1]
  ot<- order(time)
  cens<- so[ot,2]
  time<-time[ot]
  N<- nrow(so)
  hatcdist<- prodlim(Surv(time,cens)~1,reverse = TRUE)
  #censoring weights (reverse Kaplan-Meier)
  csurv<-predict(hatcdist, times=time, type = "surv")
  csurv[csurv==0]<-Inf #access infinite value to censored
  btime<-time
  # matrix transpose of survival predictions
  survs<- t(as.matrix(preds))
  
  bsc<- rep(0, nrow(survs))
  bsk<- rep(0, nrow(survs))
  bsp<- rep(0, nrow(survs))
  
  
  for (j in 1:nrow(survs)){
    
    
    help1<-as.integer(time<= btime[j] & cens == 1)
    help2<-as.integer(time>btime[j])
    
    # As the log of zero cannot be taken, values of 1 and 0
    # need to be modified: values of 1 are lowered by
    # 0.000001, values of 0 increased.
    inb <- survs[j,]
    inb[which(inb == 1)] <-(inb[which(inb == 1)]- 0.000001)
    inb[which(inb == 0)] <-(inb[which(inb == 0)]+ 0.000001)
    # Calculating brier scores for each unique time j, weighted by
    # the censoring distribution csurv
    
    bsc[j]<- mean((0 - survs[j,])^2 * help1 * (1/csurv) + (1-survs[j,])^2 * help2 * (1/csurv[j]))
    # calculating KL scores for each unique time j, weighted
    # by the censoring distribution csurv. surv[j,] has been
    #replaced by inb (defined above) to solve the problem of
    #extreme predictions.
    bsk[j]<- -mean((log(1-(inb))* help1*(1/csurv) + log(inb)*(1/csurv[j])*help2))
    bsp[j]<- -mean((log(1-survs[j,])*help1*(1/csurv) + log(survs[j,])*help2*(1/csurv[j])))
  }
  ind.values<-seq(1,5)
  rel.vals<- vector("numeric", length(ind.values))
  for (i in 1:length(ind.values)) {
    rel.vals[[i]]<-which.min(abs(btime-ind.values[i]))
  }
  Brie <- bsc[rel.vals]
  KL<- bsk[rel.vals]
  RET<- rbind(Brie,KL)
  return(RET)
}


#Variable importance function
pretty.picture.func<-function(model.nnet){
  #names input nodes
  names<- model.nnet$coefnames
  
  #number input nodes
  no.input<-model.nnet$n[1]
  
  #number hidden nodes
  no.nodes<-model.nnet$n[2]
  
  #number output nodes
  no.outputs<- model.nnet$n[3]
  rainbowcols<-rainbow(length(names), s=0.5)
  
  #dimensions for weight matrices
  ncols.1<-(no.input + 1)
  nrows.1<-(no.nodes)
  ncols.2<-(no.nodes+1)
  nrows.2<-no.outputs
  length.1<-ncols.1*nrows.1
  length.2<-ncols.2*nrows.2
  
  #selecting weights
  wts<-model.nnet$wts
  weights1<- as.data.frame(matrix(wts[1:length.1], ncol = ncols.1, nrow = nrows.1, byrow = TRUE))
  colnames(weights1)<-c("Bias", names)
  rownames(weights1)<-paste("N", seq(1:no.nodes), seq="")
  weights2<-t(matrix(wts[(length.1+1):(length.1+length.2)],nrow = nrows.2, ncol = ncols.2, byrow = TRUE))
  rownames(weights2)<-c("Bias",paste("N", seq(1:no.nodes), sep = ""))
  
  #calculating variable contribution using the
  # connection weight approach
  
  mega.mat<- matrix(NA, ncol = no.input, nrow = no.outputs)
  for (i in 1:no.input) {
    for (j in 1:no.outputs) {
      mega.mat[j,i]<-sum(weights1[, i+1]* weights2[2:(no.nodes+1),j])
    }
  }
  colnames(mega.mat)<-names
  mega.mat.abs<-abs(mega.mat)
  totals<- rowSums(mega.mat.abs)
  mega.mat.rel<-as.data.frame(mega.mat.abs/totals)
  rainbowcols<-rainbow(length(names), s = 0.5)
  rels<- as.vector(as.numeric(mega.mat.rel))
  barplot(rels, col = rainbowcols, names.arg = names, ylim = c(0,0.4), ylab = "Relative_importance")
}


#Cross-validation neural network function. Takes as arguments
# a training set, node size and decay parameter.

other.neur<- function(training_data, node.size, decay.par){
  set.seed (1245)
  
  #transforming training data
  dat.try<-data_train(training_data)
  dat.try<-dat.try[order(dat.try$id, dat.try$interval),]
  
  #Definig folds
  K<- 5
  index<- rep(1:K, floor(nrow(training_data)/K)+1)[1:nrow(training_data)]
  set.seed(92874)
  fold.index<-sample(index)
  
  
  #empty vectors for error measures
  error.val<- vector("numeric", K)
  acc<- vector("numeric", K)
  sens <- vector("numeric", K)
  spec <- vector("numeric", K)
  brier<- NULL
  KL<-NULL
  
  for (k in 1:K) {
    # indicator vector for training set in wide format data
    inda <- which(fold.index!=k)
    
    #selecting individuals using the id vector
    ids<- training_data$id[inda]
    
    #selecting individuals using the id vector
    ind.p<- which(dat.try$id %in% ids)
    
    training <- dat.try[ind.p,]
    
    #Selecting test set (test_data) from wide format data
    
    ind.ts<- which(fold.index==k)
    test.dat <- training_data[ind.ts,]
    
    #Transforming test using the test transformation function
    test<- data_test(test.dat)
    
    #Assigning interval column to separate vector
    #prior to normalization
    
    interval.test <- test$interval
    test$interval<-scale(test$interval)
    
    #Vectors are defined for the variables, because specifying
    #a dataframe instead causes the predict() function to malfunction
    Birth<- training$status
    Time <- training$Marriage_to_first_birth
    Cohabitation<- training$data2
    Circumcision<- training$Circumcision
    Region<- training$Region
    Residence<- training$Residence
    Religion<- training$Religion
    Education<- training$Education
    interval<- scale(training$interval)
    stat<- training$stat
    
    new.n.net<- nnet(cbind(stat) ~  Region + 
                       Religion + Residence + Circumcision + 
                       Education + interval, size = node.size, maxit = 2000, MaxNWts = 10000, decay = decay.par, entropy = TRUE)
    
    predict.neur <- predict(new.n.net, test, type = "raw")
    
    #data frame with prediction, prediction times, id, status
    # and original survival time in long format
    
    coll <- as.data.frame(cbind(predict.neur, test$survival, test$id, test$stat))
    
    colnames(coll) <- c("prob", "surv", "id", "stat")
    
    stat <- test.dat$stat
    idd <- unique(coll$id)
    
    # obtaining survival interval
    
    surv.id<- coll[, c(2,3)]
    real.surv <- unlist(lapply(split(surv.id, surv.id$id),
                               function(x){
                                 a<- x$surv
                                 b <- a[1]
                                 return(b)
                               }))
    
    
    # obtaining survival estimates
    coll.s<- coll[, c(1,3)]
    coll.s<- split(coll.s, coll$id)
    coll.t<- lapply(coll.s, function(x) {
      x <-  cumprod(1-x$prob)
    })
    
    
    #obtaining prediction matrix
    pred.matrix <- do.call("rbind", coll.t)
    
    #obtaining relevant survival estimate
    rel.probs<-vector("numeric", length(coll.t))
    for (i in 1:length(coll.t)) {
      temp<-coll.t[[i]]
      ind<- which(sort(unique(interval.test)) == real.surv[i])
      rel.probs[i]<- temp[ind]
    }
    
    #dataframe with probabilities, status, id and interval
    
    statt<- as.data.frame(cbind(as.data.frame(rel.probs), stat, idd, real.surv))
    colnames(statt)<- c("pred", "stat", "id", "surv")
    
    hmstat <- statt
    
    #rounding predicted probabilities to classify
    #individuals as yes/no event
    
    hmstat$pred<- 1-round(hmstat$pred, 0)
    
    #saving error values
    
    error.val[k]<-new.n.net$value
    acc[k]<-length(which(hmstat$pred == hmstat$stat))/nrow(hmstat)
    sens[k]<- length(which(hmstat$pred == 1 & hmstat$stat == 1))/length(which(hmstat$stat == 1))
    spec[k]<- length(which(hmstat$pred == 0 & hmstat$stat == 0))/ length(which(hmstat$stat == 0))
    brierKL<- brier_function.neur(statt, pred.matrix)
    brier<- rbind(brier, brierKL[1,])
    KL <- rbind(KL, brierKL[2,])
  }
  
  lst <- list()
  lst[[1]]<- cbind(error.val, acc, sens, spec)
  lst[[2]]<- brier
  lst[[3]]<- KL
  obj<- lst
  return(obj)
}

# function for applying previously defined cross-validation
#function over different numbers of nodes for a given decay 
#parameter. Returns a list with accuracy, sensitivity, specificity,
# and the cross-entropy error value as the first
#element, the Brier scores for 1-8 years as the thirs list element.

cross.val.plots<- function(decay, neuron.range){
  set.seed (1245)
  
  #for the specified decay, an object is created for each
  #number of hidden nodes, saved in a list.
  #each list element contains a list with the cross-validated
  #values of the measures in elements 1, 2, 3:
  #1) error value, accuracy, sensitivity, specificity
  #2) brier scores for every year from 1 to 8 years
  #3) KL scores for every year from 1 to 8 years
  
  objects <- list()
  for (i in 1:length(neuron.range)) {
    objects[[i]]<- other.neur(training_data, neuron.range[i], decay)
  }
  
  # the means of the measures are calculated over the folds
  
  means<-list()
  for (i in 1:length(objects)) {
    means[[i]]<- lapply(objects[[i]], colMeans)
  }
  #the sds of the measures are calculated over the folds
  sds <- list()
  for (i in 1:length(objects)) {
    sds[[i]] <- lapply(objects[[i]], function(x){
      sds<- vector("numeric", ncol(x))
      for (i in 1:ncol(x)) {
        sds[i]<- sd(x[,i])
      }
      return(sds)})
  }
  
  # the means for error value, accuracy, sensitivity, specificity
  # are collected in a matrix
  
  single.vals.0.m<- matrix(NA, nrow = length(neuron.range), ncol = 4)
  for (i in 1:length(neuron.range)) {
    single.vals.0.m[i,]<-means[[i]][[1]]
  }
  
  #the sds for error value, accuracy, sensitivity
  #specificity are collected in a matrix
  
  single.vals.0.s<- matrix(NA, nrow = length(neuron.range), ncol = 4)
  for (i in 1:length(neuron.range)) {
    single.vals.0.s[i,]<-sds[[i]][[1]]
  }
  
  # the means for the brier scores are collected in a matrix
  briers<- matrix(NA, nrow = length(neuron.range), ncol = 8)
  for (i in 1:length(neuron.range)) {
    briers[i,]<-means[[i]][[2]]
  }
  
  # the sds for the brier scores are collected in a matrix
  briers.s<- matrix(NA, nrow = length(neuron.range), ncol = 8)
  for (i in 1:length(neuron.range)) {
    briers.s[i,]<-sds[[i]][[2]]
  }
  
  # the means for the KL scores are collected in a matrix
  KLs<- matrix(NA, nrow = length(neuron.range), ncol = 8)
  for (i in 1:length(neuron.range)) {
    KLs[i,]<-means[[i]][[3]]
  }
  
  # the sds for the KL scores are collected in a matrix
  KLs.s<- matrix(NA, nrow = length(neuron.range), ncol = 8)
  for (i in 1:length(neuron.range)) {
    KLs.s[i,]<-sds[[i]][[3]]
  }
  
  # all the matrices are saved in a list
  bothlist <- list()
  bothlist[[1]]<-single.vals.0.m
  bothlist[[2]]<- briers
  bothlist[[3]]<-KLs
  
  both.list.s<- list()
  both.list.s[[1]]<- single.vals.0.s
  both.list.s[[2]]<- briers.s
  both.list.s[[3]]<- KLs.s
  
  all.list <- list()
  all.list[[1]]<- bothlist
  all.list[[2]]<- both.list.s
  
  return(all.list)
}

#RESULTS


#network is rerun every time and a new lines()
#object is plotted

#funtion for calculating performance measures

final.other.neur<- function(training_data, test_data, node.size, decay.par){
  set.seed (1245)
  training_data<-training_data[order(training_data$id),]
  test_data<-test_data[order(test_data$id),]
  
  training<-data_train(training_data)
  test<-data_test(test_data)
  
  interval.test<- test$interval
  surv.test<-test$survival
  
  test$interval<- scale(test$interval)
  
  Birth<- training$status
  Time <- training$Marriage_to_first_birth
  Cohabitation<- training$data2
  Circumcision<- training$Circumcision
  Region<- training$Region
  Residence<- training$Residence
  Religion<- training$Religion
  Education<- training$Education
  interval<- scale(training$interval)
  stat<- training$stat
  
  new.n.net<- nnet(cbind(stat) ~  Region + 
                     Religion + Residence + Circumcision + 
                     Education + interval, size = node.size, maxit = 2000, MaxNWts = 10000, decay = decay.par, entropy = TRUE)
  
  predict.neur <- predict(new.n.net, test, type = "raw")
  predict.neur<-predict.neur[,1]
  
  #data frame with prediction, prediction times, id, status
  # and original survival time in long format
  
  coll <- as.data.frame(cbind(predict.neur, test$survival, test$id, test$stat))
  
  ITs<- sort(unique(training_data$time), decreasing = FALSE)
  
  colnames(coll) <- c("prob", "surv", "id", "stat")
  
  stat <- test_data$stat
  idd <- unique(coll$id)
  
  # obtaining survival interval
  
  surv.id<- coll[, c(2,3)]
  real.surv <- unlist(lapply(split(surv.id, surv.id$id),
                             function(x){
                               a<- x$surv
                               b <- a[1]
                               return(b)
                             }))
  
  
  # obtaining survival estimates
  coll.s<- coll[, c(1,3)]
  coll.s<- split(coll.s, coll$id)
  coll.t<- lapply(coll.s, function(x) {
    x <-  cumprod(1-x$prob)
  })
  
  
  #obtaining prediction matrix
  pred.matrix <- do.call("rbind", coll.t)
  pred.matrix<- pred.matrix[order(real.surv),]
  
  #obtaining relevant survival estimate
  rel.probs<-vector("numeric", length(coll.t))
  for (i in 1:length(coll.t)) {
    temp<-coll.t[[i]]
    ind<- which(sort(unique(interval.test)) == real.surv[i])
    rel.probs[i]<- temp[ind]
  }
  
  #dataframe with probabilities, status, id and interval
  
  statt<- as.data.frame(cbind(as.data.frame(rel.probs), stat, idd, real.surv))
  colnames(statt)<- c("pred", "stat", "id", "surv")
  
  hmstat <- statt
  
  #rounding predicted probabilities to classify
  #individuals as yes/no event
  
  hmstat$pred<- 1-round(hmstat$pred, 0)
  
  #saving error values
  
  error.val<-new.n.net$value
  acc<-length(which(hmstat$pred == hmstat$stat))/nrow(hmstat)
  sens<- length(which(hmstat$pred == 1 & hmstat$stat == 1))/length(which(hmstat$stat == 1))
  spec<- length(which(hmstat$pred == 0 & hmstat$stat == 0))/ length(which(hmstat$stat == 0))
  brieKL<- brier_function.neur(statt, pred.matrix)
  brier<- brieKL[1,]
  KL <- brieKL[2,]
  
  lst <- list()
  lst[[1]]<- cbind(error.val, acc, sens, spec)
  lst[[2]]<- brier
  lst[[3]]<- KL
  obj<- lst
  plot1<-plotnet(new.n.net)
  detail<-summary(new.n.net)
  VI<-pretty.picture.func(new.n.net)
  return(obj)
  return(new.n.net)
  return(plot1)
  return(detail)
  return(VI)
}


#final result plot


cox.rep.brier.KL<- brier_nnet.cox.m(cox.statt, cox.pred.matrix)
final.rep<- final.other.neur(training_data, test_data, 5, 0.05)

plot(cox.rep.brier.KL[1,]~seq(1,5), type="l", ylim = c(0,1),
     ylab = "Brier/KL_score", xlab = "Time (days)", lwd = 2)

lines(final.rep[[2]]~seq(1,4), type="l", ylim = c(0, 0.5), col = "red",
      lwd = 2)
lines(final.rep[[3]]~seq(1,4), type="l", ylim = c(0, 0.5), col = "red",
      lwd = 2, lty = 2)
lines(cox.rep.brier.KL[2,]~seq(1,5), type="l", ylim = c(0, 0.5),
      col = "black", lwd = 2, lty = 2)

legend("topright", legend = c("Cox_Brier", "Cox_KL", "Neural_Brier", "Neural_KL"), col = c("black", "black", "red", "red"), lty = c(1,2,1,2),
       lwd = 2, bty = "n")



#prediction matrix for network with 5 nodes, 0.05 decay


#Cox model
cox.rep<- coxph(Surv(time, status) ~ factor(Region) + 
                  factor(Religion) + factor(Residence) + factor(Circumcision) + 
                  factor(Education), data = cox.train, x = TRUE, y = TRUE)

#Test for proportionality assumption

cox.prop<- cox.zph(cox.rep, transform = "km", global = TRUE)
cox.prop
ggcoxfunctional(Surv(time, status)~age_cohabitation, data = cox.train, 
                xlab="Age at first marriage")

#obtaining prediction matrix
time=cox.test$time
time=as.vector(time)
preds.rep.b<- predictSurvProb(cox.rep, cox.test, times = time)

#Making table with hazard ratios and conf intervals

tempcoefs<-summary(cox.rep)$coefficients[,c(1,3)]
HRs<- exp(tempcoefs[,1])
HRs<- round(HRs,3)
lower<-round(exp(tempcoefs[,1]-1.96*tempcoefs[,2]),2)
upper<-round(exp(tempcoefs[,1]+1.96*tempcoefs[,2]),2)
confint<-paste(lower, upper, sep = "-")
table.coefs<-cbind(HRs, confint)
#rownames(table.coefs)<- c("")
colnames(table.coefs)<- c("Hazard ratio", "95% CI")

#Obtaining acc, sens and spec for Cox
preds.rep<-diag(preds.rep.b)

stats.cox.rep<- as.data.frame(cbind(preds.rep, cox.test$time, cox.test$status))
colnames(stats.cox.rep)<- c("pred", "surv", "stat")

mod.stats.cox.rep<-stats.cox.rep
mod.stats.cox.rep$pred<- 1- round(mod.stats.cox.rep$pred, 0)

cox.rep.acc<-length(which(mod.stats.cox.rep$pred == mod.stats.cox.rep$stat))/nrow(mod.stats.cox.rep)
cox.rep.sens<- length(which(mod.stats.cox.rep$pred == 1 & mod.stats.cox.rep$stat == 1))/length(which(mod.stats.cox.rep$stat == 1))
cox.rep.spec<- length(which(mod.stats.cox.rep$pred == 0 & mod.stats.cox.rep$stat == 0))/ length(which(mod.stats.cox.rep$stat == 0))

cox.statt<- as.data.frame(cbind(cox.test$time, cox.test$status))
colnames(cox.statt)<- c("surv", "stat")
cox.pred.matrix<- predictSurvProb(cox.rep, cox.test, times = as.vector(cox.test$time))
brier_nnet.cox.m(cox.statt, cox.pred.matrix)


#Table accuracy, sensitivity, specificity, neural and Cox

final.ref<- final.other.neur(training_data, test_data, 1, 0.05)
vals.fin.ref<- cbind(as.vector(final.ref[[1]]), 
                     c(NA, cox.rep.acc, cox.rep.sens, cox.rep.spec))

rownames(vals.fin.ref)<- c("Error value", "Accuracy", "Sensitivity", "Specificity")
colnames(vals.fin.ref)<-c("Neural (0 decay, 4 nodes)", "Cox model")
vals.fin.ref



plot(survfit(Surv(data$Age_Marriage, data$Status)~1), xlab = "Age at first marriage", ylab = "Survival probability")
hist(data$Age_Marriage[which(data$Status == 1)], xlab = "Age at first marriage", main = "")

#obtaining prediction matrix
time=cox.test$time
time=as.vector(time)
preds.aft<- predict(aft.rep, cox.test, times = time)
preds.aft
#Obtaining acc, sens and spec for Cox
preds.rep<-diag(preds.rep.b)

stats.cox.rep<- as.data.frame(cbind(preds.rep, cox.test$time, cox.test$status))
colnames(stats.cox.rep)<- c("pred", "surv", "stat")

mod.stats.cox.rep<-stats.cox.rep
mod.stats.cox.rep$pred<- 1- round(mod.stats.cox.rep$pred, 0)

cox.rep.acc<-length(which(mod.stats.cox.rep$pred == mod.stats.cox.rep$stat))/nrow(mod.stats.cox.rep)
cox.rep.sens<- length(which(mod.stats.cox.rep$pred == 1 & mod.stats.cox.rep$stat == 1))/length(which(mod.stats.cox.rep$stat == 1))
cox.rep.spec<- length(which(mod.stats.cox.rep$pred == 0 & mod.stats.cox.rep$stat == 0))/ length(which(mod.stats.cox.rep$stat == 0))
