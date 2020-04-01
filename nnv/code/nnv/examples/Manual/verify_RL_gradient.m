clear all
close all

% install % only install once!!!

load('../../../../../DDPG/model_arrays/model1_weights.mat')
L1 = LayerS(double(weights0), double(biases0)', 'poslin'); % sigmoid, purelin, poslin(relu), tanh
L2 = LayerS(double(weights1), double(biases1)', 'poslin');
L3 = LayerS(double(weights2), double(biases2)', 'logsig');

% W1 = [1 -1 0.5; 2 -1 1]; % 2x3
% b1 = [-1; 0.5]; 
% W2 = [-2 1; 0 1; -2 -2; 3 -1];  % 4x2 
% b2 = [1;3;-2;-1];
% W3 = [1 2 3 4]; %1x4
% b3 = [2];
% L1 = LayerS(W1, b1, 'poslin'); % sigmoid, purelin, poslin, tanh
% L2 = LayerS(W2, b2, 'poslin');
% L3 = LayerS(W3, b3, 'logsig');

F = FFNNS([L1 L2 L3]); % construct an NNV FFNN

% state: s, v, dv
lb = [2; 1; -20]; % lower bound on input vector
ub = [60; 30; 20]; % upper bound on input vector
% lb = [-10; -20; -10]; % lower bound vector
% ub = [10; 10; 20]; % upper bound vector

%/* Compute and plot gradient
% n =  5 ; % discretization points
% test_ind = 2; % analyze gradient on which state
% x_fixed = [30; 15; 0]; % fixed input value to evaluate F.gradient()
% plot_gradient(F,ub,lb,test_ind,x_fixed,n)

I = Star(lb, ub); % star input set
B = Box(lb, ub); % a box input set
I_Zono = B.toZono; % convert to a zonotope

%/* Properties
P = HalfSpace(1, 0); % P: y >= 0, safe region
%/* verify the network
nC = 1; % number of cores
nS = 0; % number of samples

map_mat = eye(1); % mapping matrix
map_vec = []; % mapping vector
P_poly = Polyhedron('A', P.G, 'b', P.g); % polyhedron obj


figure;
% subplot(2, 2, 1);
[safe1, t1, cE1] = F.verify(I, P, 'exact-star', nC, nS);
F.visualize(map_mat, map_vec); % plot y1 y2
hold on;
plot(P_poly); % plot unsafe region
title('exact-star', 'FontSize', 13);

% subplot(2,2,2);
% [safe2, t2, cE2] = F.verify(I, P, 'approx-star', nC, nS);
% F.visualize(map_mat, map_vec); % plot y1 y2
% hold on;
% plot(P_poly); % plot unsafe region
% title('approx-star', 'FontSize', 13);

% subplot(2,2,3);
% [safe3, t3, cE3] = F.verify(I_Zono, P, 'approx-zono', nC, nS);
% F.visualize(map_mat, map_vec); % plot y1 y2
% hold on;
% plot(P_poly); % plot unsafe region
% title('approx-zono', 'FontSize', 13);
% 
% subplot(2, 2, 4);
% [safe4, t4, cE4] = F.verify(I, P, 'abs-dom', nC, nS);
% F.visualize(map_mat, map_vec); % plot y1 y2
% hold on;
% plot(P_poly); % plot unsafe region
% title('abs-dom', 'FontSize', 13);






%% functions

function plot_gradient(F,ub,lb, test_ind, x_fixed,n)

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

% evaluate the input vectors using the original F and its gradient version
for i = 1:numel(test_var)
    yp(i,:)=F.gradient(X(:,i));
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
plot(test_var,yp(:,test_ind),'LineWidth',2);
xlabel(sprintf('x%d',test_ind)); ylabel('f prime(x)')
title('input - output gradient')

end