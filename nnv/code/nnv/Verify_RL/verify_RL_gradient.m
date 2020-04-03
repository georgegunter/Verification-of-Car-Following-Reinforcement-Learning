% clear all
% close all

% install

%% Load RL controller model
load('../../../../DDPG/model_arrays/model1_weights.mat')
L1 = LayerS(double(weights0), double(biases0)', 'purelin'); % sigmoid, purelin, poslin(relu), tanh
L2 = LayerS(double(weights1), double(biases1)', 'purelin');
L3 = LayerS(double(weights2), double(biases2)', 'logsig');

F = FFNNS([L1 L2 L3]); % construct an NNV FFNN

%% Verify F using output reachable set NNV toolbox

% set state boundaries: s, v, dv
lb = [2; 10; -5]; % lower bound on input vector
ub = [40; 40; 5]; % upper bound on input vector

I = Star(lb, ub); % star input set

%/* properties
P1 = HalfSpace(1, -2); % P: y >= -2, safe region
P2 = HalfSpace(-1, -2); % P: y <= 2, safe region

%/* verify the network
nC = 1; % number of cores
nS = 0; % number of samples

map_mat = eye(1); % mapping matrix
map_vec = []; % mapping vector
P_poly1 = Polyhedron('A', P1.G, 'b', P1.g); % polyhedron obj
P_poly2 = Polyhedron('A', P2.G, 'b', P2.g); % polyhedron obj

figure;
[safe2, t2, cE2] = F.verify(I, P1, 'approx-star', nC, nS);
F.visualize(map_mat, map_vec); % plot y1 y2
hold on;
plot(P_poly1); % plot unsafe region
plot(P_poly2); % plot unsafe region
xlim([-5, 5])
legend('Controller output range','','unsafe region1','','unsafe region2')
title('Controller output range - approx-star', 'FontSize', 13);

%% symbolic output interval calculation
syms a [F.nI 1] rational real
dfdx = F.symbolicGradient(a); % size: nO x nI

%% find gradient bounds by fminsearchbnd
dfds = matlabFunction(dfdx(1),'vars', {[a1 a2 a3].'}); % dfds > 0
dfdv_n = matlabFunction(-dfdx(2),'vars', {[a1 a2 a3].'}); % dfdv < 0
dfddv = matlabFunction(dfdx(3),'vars', {[a1 a2 a3].'}); % dfddv > 0

x0 = [30; 15; 0]; % fixed input value to evaluate dfdx
[sol_ds,dfds_min] = fminsearchbnd(dfds,x0,lb,ub); % rational if > 0
[sol_dv,dfdv_max] = fminsearchbnd(dfdv_n,x0,lb,ub); % rational if < 0
[sol_ddv,dfddv_min] = fminsearchbnd(dfddv,x0,lb,ub); % rational if > 0

if dfds_min > 0 && dfdv_max < 0 && dfddv_min > 0
    disp('Rational driving constraints satisfied given input bounds\n')
else
    if dfds_min < 0
        fprintf('Rational driving constraints violated: dfds < 0 at %s\n ',num2str(sol_ds'))
        x0 = sol_ds;
    end
    if dfdv_max > 0
        fprintf('Rational driving constraints violated: dfdv > 0 at %s\n',num2str(sol_dv'))
        x0 = sol_dv;
    end
    if dfddv_min < 0
        fprintf('Rational driving constraints violated: dfddv > 0 at %s\n',num2str(sol_ddv'))
        x0 = sol_ddv;
    end   
end

%% plot gradient wrt one state
state = {'s','v','dv'};
rdc = {' > 0',' < 0',' > 0'};

figure('Position',[180 180 300*F.nI 300])
for x_ind = 1:F.nI % state index
    a_copy = a; a_copy(x_ind)=[];
    x0_copy = x0; x0_copy(x_ind)=[];
    dfdx_ind = matlabFunction(subs(dfdx,a_copy,x0_copy));
    subplot(1,F.nI,x_ind)
    fplot(dfdx_ind,[lb(x_ind) ub(x_ind)],'LineWidth',2)
    xlabel(state(x_ind)); ylabel('dfdx')
    legend(strcat('RDC: dfd',state,rdc));
end
sgtitle("Verify rational driving constraints")

%% Evaluate the network and its gradient numerically
n = 30 ; % discretization points
plotGradient(F,ub,lb,x_ind,x0,n,dfdx) % need to optimize by fplot()

%% helper functions
function plotGradient(F,ub,lb, test_ind, x_fixed,n,dfdx)

switch test_ind
    case 1
        x1 = linspace(lb(1),ub(1),n);
        x2 = x_fixed(2) * ones(size(x1));
        x3 = x_fixed(3) * ones(size(x1));
    case 2
        x2 = linspace(lb(2),ub(2),n);
        x1 = x_fixed(1) * ones(size(x2));
        x3 = x_fixed(3) * ones(size(x2));
    case 3
        x3 = linspace(lb(3),ub(3),n);
        x1 = x_fixed(1) * ones(size(x3));
        x2 = x_fixed(2) * ones(size(x3));
end

X = [x1;x2;x3];
test_var = X(test_ind,:);

% test symbolic expression
syms a [F.nI 1] rational real
a_copy = a; a_copy(test_ind)=[];
x0_copy = x_fixed; x0_copy(test_ind)=[];
dfdx_ind = matlabFunction(subs(dfdx(test_ind),a_copy,x0_copy));

% evaluate the input vectors using the original F and its gradient version
for i = 1:numel(test_var)
%     yp(i,:)=F.gradient(X(:,i));
%     df(i,:)= vpa(subs(dfdx,a,X(:,i)));
    y(i)=F.evaluate(X(:,i));
end

% plot F output given the input range
figure('Position',[100 100 400 200])
subplot(121)
plot(test_var,y,'LineWidth',2);
xlabel(sprintf('x%d',test_ind)); ylabel('f(x)')
title('input - output')

% plot F.gradient output given input range
subplot(122)
% plot(test_var,yp(:,test_ind),'LineWidth',2);
fplot(dfdx_ind,[lb(test_ind) ub(test_ind)],'LineWidth',2)
xlabel(sprintf('x%d',test_ind)); ylabel('f prime(x)')
title('input - output gradient')

end