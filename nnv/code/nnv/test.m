clear all
close all

W1 = [1 -1 0.5; 2 -1 1]; % 2x3
b1 = [-1; 0.5]; 
W2 = [-2 1; 0 1; -2 -2; 3 -1];  % 4x2 
b2 = [1;3;-2;-1];
W3 = [1 2 3 4]; %1x4
b3 = [2];
L1 = LayerS(W1, b1, 'purelin'); % sigmoid, purelin, poslin, tanh
L2 = LayerS(W2, b2, 'purelin');
L3 = LayerS(W3, b3, 'logsig');
% load('../../../../../DDPG/model_arrays/model1_weights.mat')
% L1 = LayerS(double(weights0), double(biases0)', 'purelin'); % sigmoid, purelin, poslin(relu), tanh
% L2 = LayerS(double(weights1), double(biases1)', 'purelin');
% L3 = LayerS(double(weights2), double(biases2)', 'logsig');

F = FFNNS([L1 L2 L3]); % construct an NNV FFNN
% state: s, v, dv
lb = [2; -2; 0]; % lower bound vector
ub = [40; 1; 2]; % upper bound vector

%% symbolic output interval calculation
syms a [F.nI 1] rational real
dfdx = F.symbolicGradient(a); % no x ni

%% plot 3-d surface
% fix a1
dfdx1 = @(a2,a3)subs(dfdx,a1,30);
dfdx1 = dfdx1(1);
ezsurf(dfdx1(1),dfdx1(2),dfdx1(3),[-2 0],[1 2])

dfdx2 = @(a1,a3)subs(dfdx,a2,20);
dfdx2 = dfdx2(1);
ezsurf(dfdx2(1),dfdx2(2),dfdx2(3),[2 0],[10 2])

dfdx3 = @(a1,a2)subs(dfdx,a3,0);
dfdx3 = dfdx3(1);
ezsurf(dfdx3(1),dfdx3(2),dfdx3(3),[2 -2],[10 1])

% dfdx3 = @(a1,a2)subs(dfdx,a3,x_fixed(3));
% dfdx3 = dfdx3(1); % do not change
% figure
% surface = ezsurf(dfdx3(1),[2 40],[10 40])
% set(gca,'ZLim',[0 1.6])

% fsurf(dfdx1,[-2 2 1 10])

% assume(a, 'real')
% [limit(dfdx, a1, sym(inf)), limit(dfdx, a1, -sym(inf))]
% double(subs(dfdx(3),a,[-1;-2;1]))
% F.gradient([-1;-2;1])
FPrime = toGradient(F);
lb = ones(FPrime.nI,1); ub = lb;
I = Star(lb, ub);
P = HalfSpace(1, 0); % P: y >= 0, safe region

%/* verify the network
nC = 4; % number of cores
nS = 0; % number of samples

map_mat = eye(1); % mapping matrix
map_vec = []; % mapping vector
P_poly = Polyhedron('A', P.G, 'b', P.g); % polyhedron obj

figure;
[safe1, t1, cE1] = FPrime.verify(I, P, 'approx-star', nC, nS);
FPrime.visualize(map_mat, map_vec); % plot y1 y2
hold on;
plot(P_poly); % plot unsafe region

legend('output bound','unsafe region')
title('exact-star', 'FontSize', 13);


%%

n = 30;

test_ind = 1;

switch test_ind
    case 1
        x1 = linspace(lb(1),ub(1),n);
        x2 = 0.5 * ones(size(x1));
        x3 = 1 * ones(size(x1));     
    case 2
        x2 = linspace(lb(2),ub(2),n);
        x1 = -0.5 * ones(size(x2));
        x3 = 1 * ones(size(x2));
    case 3
        x3 = linspace(lb(3),ub(3),n);
        x2 = 0.5 * ones(size(x3));
        x1 = -0.5 * ones(size(x3));
end

X = [x1;x2;x3];

test_var = X(test_ind,:);
for i = 1:numel(test_var)
    yp(i,:)=F.gradient(X(:,i));
    y(i)=F.evaluate(X(:,i));
end

figure('Position',[100 100 400 200])
subplot(121)
plot(test_var,y,'LineWidth',2);
xlabel(sprintf('x%d',test_ind)); ylabel('f(x)')
title('input - output')

subplot(122)
plot(test_var,yp(:,test_ind),'LineWidth',2);
xlabel(sprintf('x%d',test_ind)); ylabel('f prime(x)')
title('input - output gradient')
%% functions
function FPrime = toGradient(F)
FPrime = F;
% y_sym = 

for i = 1:F.nL
    if strcmp(F.Layers(i).f, 'purelin')
        FPrime.Layers(i).b = zeros(size(F.Layers(i).b));
    elseif strcmp(obj.f, 'poslin')
        
    else % for other continuous activation functions
        y = F.Layers(i).W * F.Layers(i).b

    end
end
end
