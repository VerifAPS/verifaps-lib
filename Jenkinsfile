pipeline {
  agent {
    docker {
      image 'wadoon/verifaps-test:latest'
    }

  }
  stages {
    stage('Build') {
      steps {
        sh 'gradle classes'
      }
    }
    stage('Build-Test') {
      steps {
        sh 'gradle testClasses'
      }
    }
    stage('Check') {
      steps {
        sh 'gradle --continue -parallel --build-cache check'
      }
    }
    stage('Sonarqube') {
      steps {
        sh '''gradle sonarqube \\                                                                                                           130 / git:develop / 18:40:25
  -Dsonar.projectKey=VerifAPS_verifaps-lib \\
  -Dsonar.organization=verifaps \\
  -Dsonar.host.url=https://sonarcloud.io -Dsonar.branch.name=develop \\
  -Dsonar.login=661de2898437c19b0efc976227e55b63d09d9ea5 --parallel'''
      }
    }
  }
}