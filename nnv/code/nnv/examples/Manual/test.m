clear y yp x x1 x2 x3
close all
n = 30;

test_ind = 2;

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

figure
subplot(121)
plot(test_var,y,'LineWidth',2);
xlabel(sprintf('x%d',test_ind)); ylabel('f(x)')
title('input - output')

subplot(122)
plot(test_var,yp(:,test_ind),'LineWidth',2);
xlabel(sprintf('x%d',test_ind)); ylabel('f prime(x)')
title('input - output gradient')

