% clear all
% close all

% install

%% Load RL controller model
load('../../../../DDPG/models//Model X/model_weights_biases.mat')
L1 = LayerS(double(weights0), double(biases0)', 'tansig'); % logsig (sigmoid), purelin, poslin(relu), tanh
L2 = LayerS(double(weights1), double(biases1)', 'tansig');
L3 = LayerS(double(weights2), double(biases2)', 'tansig');

F = FFNNS([L1 L2 L3]); % construct an NNV FFNN

%% Verify F using output reachable set NNV toolbox

% set state boundaries: s, v, dv
lb = [0; 0; -5]; % lower bound on input vector
ub = [20; 8; 5]; % upper bound on input vector

I = Star(lb, ub); % star input set
B = Box(lb, ub); % a box input set
I_Zono = B.toZono; % convert to a zonotope

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
% [safe2, t2, cE2] = F.verify(I, P1, 'approx-star', nC, nS);
[safe3, t3, cE3] = F.verify(I_Zono, P1, 'approx-zono', nC, nS);

F.visualize(map_mat, map_vec); % plot
hold on;
plot(P_poly1); % plot unsafe region
plot(P_poly2); % plot unsafe region
xlim([-3, 3])
legend('Controller output range','','unsafe region1','','unsafe region2')
title('Controller output range - approx-zono', 'FontSize', 20);
xlabel('Controller output (m/s2)','FontSize', 16)

%% symbolic output interval calculation
syms a [F.nI 1] rational real
y = F.evaluate(a); % symbolic output
dfdx = F.symbolicGradient(a); % symbolic gradient output size: nO x nI

%% find output bounds by fminsearchbnd
yf = matlabFunction(y,'vars', {a});
yfn = matlabFunction(-y,'vars', {a}); 

x0 = [5; 4; 0]; 
[x_min,accel_min] = fminsearchbnd(yf,x0,lb,ub)
[x_max,val_maxn] = fminsearchbnd(yfn,x0,lb,ub);
accel_max = -val_maxn

%% find gradient bounds by fminsearchbnd
dfds = matlabFunction(dfdx(1),'vars', {a}); % dfds > 0
dfdv_n = matlabFunction(-dfdx(2),'vars', {a}); % dfdv < 0
dfddv = matlabFunction(dfdx(3),'vars', {a}); % dfddv > 0

%%
x0 = [10;4;2]; % fixed input value to evaluate dfdx
[sol_ds,dfds_min] = fminsearchbnd(dfds,x0,lb,ub); % rational if > 0
[sol_dv,dfdv_max] = fminsearchbnd(dfdv_n,x0,lb,ub); % rational if < 0
[sol_ddv,dfddv_min] = fminsearchbnd(dfddv,x0,lb,ub); % rational if > 0
dfdv_max = -dfdv_max;

if dfds_min >= 0 && dfdv_max <= 0 && dfddv_min >= 0
    disp('Rational driving constraints satisfied given input bounds')
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

%% plot gradient by numerical evaluation(low fidelity)
ns = 30;
x0 = [2, 5, 0]';
plotGradientNumeric(ub,lb, x0, F, ns)

%% Evaluate the network and its gradient using symbolic expression
x_ind = 3; % state to examine
plotGradient(ub,lb,x_ind,x0,y, dfdx)

%% Evaluate the network gradient given training episodes
state_data = readmatrix('RLmodels/state_data.csv');
% change to s,v,dv
state_data = state_data(:,[2 1 3]);
evaluateEpisodeGradient(state_data,F)

%% save data
% save('model11-tanh.mat')

%% helper functions
function plotGradient(ub,lb, test_ind, x_fixed, fx, dfdx)

% Plot the partial derivatives by fplot using the symbolic expressions
% directly
syms a [size(dfdx,2) 1] rational real
y_sym = fx;
dfdx_sym = dfdx;

a_copy = a; a_copy(test_ind)=[];
x0_copy = x_fixed; x0_copy(test_ind)=[];

y_ind = matlabFunction(subs(y_sym,a_copy,x0_copy));
dfdx_ind = matlabFunction(subs(dfdx_sym(test_ind),a_copy,x0_copy));

state = {'s','v','dv'};


% plot F output given the input range
figure('Position',[100 100 400 200])
subplot(121)
fplot(y_ind,[lb(test_ind) ub(test_ind)],'LineWidth',2)
xlabel(state{test_ind}); ylabel('f(x)')
title('original output')

% plot F.gradient output given input range
subplot(122)
fplot(dfdx_ind,[lb(test_ind) ub(test_ind)],'LineWidth',2)
xlabel(state{test_ind}); ylabel(sprintf('dfd%s',state{test_ind}))
title('gradient output')

sgtitle(sprintf('%s = %.2g ', permute(horzcat(string(a_copy), num2str(x0_copy)),[2,1])))

end

function plotGradientNumeric(ub,lb, x_fixed, F, ns)
% plot the partial derivates evaluated at the sampled points
% ns: sampling fidelity

p1 = linspace(lb(1),ub(1),ns);
p2 = linspace(lb(2),ub(2),ns);
p3 = linspace(lb(3),ub(3),ns);

x1 = x_fixed'.*ones(ns,3); x1(:,1) = p1';
x2 = x_fixed'.*ones(ns,3); x2(:,2) = p2';
x3 = x_fixed'.*ones(ns,3); x3(:,3) = p3';
x = {x1,x2,x3};

G1 = zeros(ns,3);
G2 = zeros(ns,3);
G3 = zeros(ns,3);

% evaluate
for i = 1:ns
    G1(i,:) = F.gradient(x1(i,:)');
    G2(i,:) = F.gradient(x2(i,:)');
    G3(i,:) = F.gradient(x3(i,:)');
end

G = {G1,G2,G3};
state = {'s','v','dv'};
rdc = {' > 0',' < 0',' > 0'};

figure('Position',[180 180 300*F.nI 300])
for x_ind = 1:F.nI % state index
    subplot(1,F.nI,x_ind)
    plot(x{x_ind}(:,x_ind),G{x_ind},'LineWidth',2)
    xlabel(state(x_ind)); ylabel('dfdx')
    legend(strcat('RDC: dfd',state,rdc));
end
sgtitle("Verify rational driving constraints")

end

function evaluateEpisodeGradient(data,F)

ns = size(data,1);

G = zeros(ns,3);


% evaluate
for i = 1:ns
    G(i,:) = F.gradient(data(i,:)');
end


state = {'s','v','dv'};

figure('Position',[180 180 300*F.nI 300])
for x_ind = 1:F.nI % state index
    subplot(1,F.nI,x_ind)
    plot(G(:,x_ind),'LineWidth',2)
    xlabel('Episode'); ylabel('dfdx')
    legend(strcat('dfd',state{x_ind}));
end
sgtitle("Partial derivatives")




end