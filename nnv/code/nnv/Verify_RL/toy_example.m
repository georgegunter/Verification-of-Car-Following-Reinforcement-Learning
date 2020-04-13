clear all
close all

W1 = [1 -1 0.5; 2 -1 1]; % 2x3
b1 = [-1; 0.5]; 
W2 = [-2 1; 0 1; -2 -2; 3 -1];  % 4x2 
b2 = [1;3;-2;-1];
W3 = [1 2 3 4]; %1x4
b3 = [2];
L1 = LayerS(W1, b1, 'purelin'); % sigmoid, purelin, poslin, tanh
L2 = LayerS(W2, b2, 'poslin');
L3 = LayerS(W3, b3, 'logsig');

F = FFNNS([L1 L2 L3]); % construct an NNV FFNN
% state: s, v, dv
lb = [2; 10; 2]; % lower bound vector
ub = [40; 20; 5]; % upper bound vector
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
F.visualize(map_mat, map_vec); % plot
hold on;
plot(P_poly1); % plot unsafe region
plot(P_poly2); % plot unsafe region
xlim([-5, 5])
legend('Controller output range','','unsafe region1','','unsafe region2')
title('Controller output range - approx-star', 'FontSize', 13);

%% symbolic output interval calculation
syms a [F.nI 1] rational real
y = F.evaluate(a); % symbolic output
dfdx = F.symbolicGradient(a); % symbolic gradient output size: nO x nI

%% find output bounds by fminsearchbnd
yf = matlabFunction(y,'vars', {a});
yfn = matlabFunction(-y,'vars', {a}); 

x0 = [30; 15; 0]; 
[x_min,val_min] = fminsearchbnd(yf,x0,lb,ub)
[x_max,val_maxn] = fminsearchbnd(yfn,x0,lb,ub);
val_max = -val_maxn

%% find gradient bounds by fminsearchbnd
dfds = matlabFunction(dfdx(1),'vars', {[a1 a2 a3].'}); % dfds > 0
dfdv_n = matlabFunction(-dfdx(2),'vars', {[a1 a2 a3].'}); % dfdv < 0
dfddv = matlabFunction(dfdx(3),'vars', {[a1 a2 a3].'}); % dfddv > 0

x0 = [30; 15; 0]; % fixed input value to evaluate dfdx
[sol_ds,dfds_min] = fminsearchbnd(dfds,x0,lb,ub); % rational if > 0
[sol_dv,dfdv_max] = fminsearchbnd(dfdv_n,x0,lb,ub); % rational if < 0
[sol_ddv,dfddv_min] = fminsearchbnd(dfddv,x0,lb,ub); % rational if > 0
dfdv_max = -dfdv_max;

if dfds_min >= 0 && dfdv_max <= 0 && dfddv_min >= 0
    disp('Rational driving constraints satisfied given input bounds')
else
    if dfds_min < 0
        fprintf('Rational driving constraints violated: dfds < 0 at %s\n',num2str(sol_ds'))
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
x_ind = 1; % state to examine
plotGradient(F,ub,lb,x_ind,x0)

%% helper functions
function plotGradient(F,ub,lb, test_ind, x_fixed)

% symbolic expression
syms a [F.nI 1] rational real
y_sym = F.evaluate(a);
dfdx_sym = F.symbolicGradient(a);

a_copy = a; a_copy(test_ind)=[];
x0_copy = x_fixed; x0_copy(test_ind)=[];

y_ind = matlabFunction(subs(y_sym(test_ind),a_copy,x0_copy));
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